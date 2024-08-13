package fortress.operations

import fortress.msfol._

import scala.collection.mutable

/**
  * Compiles function definitions into Scala functions on demand and evaluates them if interpretation-independent.
  */
// TODO: fix nonexhaustive match warnings here and Evaluator
class DefinitionJit(theory: Theory) {

    private type JitFunc = Seq[Option[Value]] => Option[Value]

    private val jitCache = mutable.Map[String, JitFunc]()
    private val resultCache = mutable.Map[(String, Seq[Option[Value]]), Option[Value]]()

    /**
      * Evaluate defn at args and return the value result, or None if the result is interpretation-dependent.
      * The JIT function will be cached and used for subsequent evaluations of this interpretation.
      */
    def evaluate(defn: FunctionDefinition, args: Seq[Option[Value]]): Option[Value] =
        resultCache.getOrElseUpdate((defn.name, args), compile(defn)(args))

    // Compile the definition and return the corresponding JIT function.
    private def compile(defn: FunctionDefinition): JitFunc = jitCache.getOrElseUpdate(defn.name, {
        val varIdxs = defn.argSortedVar.map(_.variable).zipWithIndex.toMap
        compileTerm(defn.body, varIdxs)
    })

    // JIT the term to a function. varIdxs is the mapping from variable names to indices in the argument list.
    private def compileTerm(term: Term, varIdxs: Map[Var, Int]): JitFunc = term match {
        case Top => _ => Some(Top)
        case Bottom => _ => Some(Bottom)
        case de @ DomainElement(_, _) => _ => Some(de)

        case v @ Var(_) => varIdxs.get(v) match {
            // If not in varIdxs, it must be a constant; TODO handle cDefs?
            case None => _ => None
            // It's in varIdxs: return the idx'th argument
            case Some(idx) => args => args(idx)
        }

        case App(name, appArgs) => theory.functionDefinitions find (_.name == name) match {
            // We can only evaluate calls to definitions
            case None => _ => None
            // JIT the called definition and evaluate it
            case Some(fDef) =>
                val jitAppArgs = appArgs map (compileTerm(_, varIdxs))
                args => evaluate(fDef, jitAppArgs.map(argFunc => argFunc(args)))
        }

        // JIT boolean operations (3-valued logic)
        case Not(sub) =>
            val jitSub = compileTerm(sub, varIdxs)
            args => jitSub(args) map {
                case Top => Bottom
                case Bottom => Top
            }
        case AndList(conjuncts) =>
            val jitConjuncts = conjuncts map (compileTerm(_, varIdxs))
            args => jitConjuncts map (conjunctFunc => conjunctFunc(args)) reduce { (a, b) => (a, b) match {
                case (Some(Top), x) => x // true && x == x, even for x == unknown
                case (x, Some(Top)) => x // x && true == x, even for x == unknown
                case (Some(Bottom), _) => Some(Bottom) // false && x == false, even for x == unknown
                case (_, Some(Bottom)) => Some(Bottom) // x && false == false, even for x == unknown
                case (None, None) => None // unknown && unknown == unknown
            }}
        case OrList(disjuncts) =>
            val jitDisjuncts = disjuncts map (compileTerm(_, varIdxs))
            args => jitDisjuncts map (disjunctFunc => disjunctFunc(args)) reduce { (a, b) => (a, b) match {
                case (Some(Top), _) => Some(Top) // true || x == true, even for x == unknown
                case (_, Some(Top)) => Some(Top) // x || true == true, even for x == unknown
                case (Some(Bottom), x) => x // false || x == x, even for x == unknown
                case (x, Some(Bottom)) => x // false || x == x, even for x == unknown
                case (None, None) => None // unknown || unknown == unknown
            }}
        case Distinct(distArgs) =>
            val jitDistArgs = distArgs map (compileTerm(_, varIdxs))
            args => {
                val evalDistArgs = jitDistArgs map (distArgFunc => distArgFunc(args))
                // If any two are the same, we aren't distinct; otherwise if any unknown, unknown; else distinct
                val knownDistArgs = evalDistArgs filter (_.nonEmpty) map (_.get)
                if (knownDistArgs.distinct.size != knownDistArgs.size) Some(Bottom)
                else if (knownDistArgs.size < evalDistArgs.size) None
                else Some(Top)
            }
        case Implication(left, right) =>
            val jitLeft = compileTerm(left, varIdxs)
            val jitRight = compileTerm(right, varIdxs)
            args => jitLeft(args) flatMap {
                case Top => jitRight(args) // (true => x) == x for all x
                case Bottom => Some(Top) // (false => x) == true for all x
            }
        case Iff(left, right) => evalEqIff(left, right, varIdxs)
        case Eq(left, right) => evalEqIff(left, right, varIdxs)
        case IfThenElse(condition, ifTrue, ifFalse) =>
            val jitCondition = compileTerm(condition, varIdxs)
            val jitIfTrue = compileTerm(ifTrue, varIdxs)
            val jitIfFalse = compileTerm(ifFalse, varIdxs)
            args => jitCondition(args) flatMap {
                case Top => jitIfTrue(args)
                case Bottom => jitIfFalse(args)
            }

        // Evaluate integers
        case i @ IntegerLiteral(_) => _ => Some(i)
        case BuiltinApp(IntNeg, Seq(x)) =>
            val jitX = compileTerm(x, varIdxs)
            args => jitX(args) map {
                case IntegerLiteral(i) => IntegerLiteral(-i)
            }
        case BuiltinApp(IntPlus, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i + j)
            }
        case BuiltinApp(IntSub, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i - j)
            }
        case BuiltinApp(IntMult, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i * j)
            }
        case BuiltinApp(IntDiv, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) flatMap {
                case (IntegerLiteral(_), IntegerLiteral(0)) => None // do not evaluate div-by-zero
                case (IntegerLiteral(i), IntegerLiteral(j)) => Some(IntegerLiteral(i / j))
            }
        case BuiltinApp(IntMod, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) flatMap {
                case (IntegerLiteral(_), IntegerLiteral(0)) => None // do not evaluate mod-by-zero
                case (IntegerLiteral(i), IntegerLiteral(j)) => Some(IntegerLiteral(i % j))
            }
        case BuiltinApp(IntLE, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i <= j)
            }
        case BuiltinApp(IntLT, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i < j)
            }
        case BuiltinApp(IntGE, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i >= j)
            }
        case BuiltinApp(IntGT, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i > j)
            }

        // Evaluate BitVectors
        case bv @ BitVectorLiteral(_, _) => _ => Some(bv)
        case BuiltinApp(BvNeg, Seq(x)) =>
            val jitX = compileTerm(x, varIdxs)
            args => jitX(args) map {
                case BitVectorLiteral(i, bitwidth) => wrapBv(-i, bitwidth)
            }
        case BuiltinApp(BvPlus, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i + j, bw1)
            }
        case BuiltinApp(BvSub, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i - j, bw1)
            }
        case BuiltinApp(BvMult, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i * j, bw1)
            }
        case BuiltinApp(BvSignedDiv, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) flatMap {
                case (_, BitVectorLiteral(0, _)) => None // don't try and handle div-by-zero here
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => Some(wrapBv(i / j, bw1))
            }
        case BuiltinApp(BvSignedMod, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) flatMap {
                case (_, BitVectorLiteral(0, _)) => None // don't try and handle mod-by-zero here
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 =>
                    // In BvSignedMod, the sign follows the divisor (second argument)
                    // https://z3prover.github.io/api/html/group__capi.html#ga9f99e96fc60cb67789fab87be0ba5919
                    val result = (i.abs % j.abs) * j.sign
                    Some(wrapBv(result, bw1))
            }
        case BuiltinApp(BvSignedRem, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) flatMap {
                case (_, BitVectorLiteral(0, _)) => None // don't try and handle rem-by-zero here
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 =>
                    // In BvSignedRem, the sign follows the dividend (first argument)
                    // https://z3prover.github.io/api/html/group__capi.html#ga9f99e96fc60cb67789fab87be0ba5919
                    val result = (i.abs % j.abs) * i.sign
                    Some(wrapBv(result, bw1))
            }
        case BuiltinApp(BvSignedLE, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i <= j)
            }
        case BuiltinApp(BvSignedLT, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i < j)
            }
        case BuiltinApp(BvSignedGE, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i >= j)
            }
        case BuiltinApp(BvSignedGT, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i > j)
            }
        case BuiltinApp(BvConcat, Seq(x, y)) =>
            val jitX = compileTerm(x, varIdxs)
            val jitY = compileTerm(y, varIdxs)
            args => (jitX(args) zip jitY(args)) map {
                case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) => BitVectorLiteral((i << bw2) | j, bw1 + bw2)
            }

        // TODO: Evaluate quantifiers by expanding?
        case Forall(_, _) => _ => None
        case Exists(_, _) => _ => None

        // TODO: Evaluate closures. (Currently, run this after closure elimination).
        case Closure(_, _, _, _) => _ => None
        case ReflexiveClosure(_, _, _, _) => _ => None
    }

    private def evalEqIff(left: Term, right: Term, varIdxs: Map[Var, Int]): JitFunc = {
        val jitLeft = compileTerm(left, varIdxs)
        val jitRight = compileTerm(right, varIdxs)
        args => (jitLeft(args) zip jitRight(args)) map {
            case (evalLeft, evalRight) => fromBool(evalLeft == evalRight)
        }
    }

    private def fromBool(bool: Boolean): Value = if (bool) Top else Bottom

    private def wrapBv(value: Int, bitwidth: Int): BitVectorLiteral =
        BitVectorLiteral(value & ((1 << bitwidth) - 1), bitwidth)

}
