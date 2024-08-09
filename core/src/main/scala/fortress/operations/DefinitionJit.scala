package fortress.operations

import fortress.msfol._
import fortress.util.Errors

import scala.collection.mutable

/** Compiles function definitions into Scala functions on demand. */
// TODO: fix nonexhaustive match warnings here and Evaluator
class DefinitionJit(theory: Theory) {

    private type JitFunc = Seq[Option[Value]] => Option[Value]

    private val jitCache = mutable.Map[String, JitFunc]()
    private val resultCache = mutable.Map[(String, Seq[Option[Value]]), Option[Value]]()

    def evaluate(defn: FunctionDefinition, args: Seq[Option[Value]]): Option[Value] =
        resultCache.getOrElseUpdate((defn.name, args), compile(defn)(args))

    private def compile(defn: FunctionDefinition): JitFunc = jitCache.getOrElseUpdate(defn.name, {
        val varIdxs = defn.argSortedVar.map(_.variable).zipWithIndex.toMap
        compileTerm(defn.body, varIdxs)
    })

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
        case Iff(left, right) =>
            val jitLeft = compileTerm(left, varIdxs)
            val jitRight = compileTerm(right, varIdxs)
            args => (jitLeft(args) zip jitRight(args)) map {
                case (evalLeft, evalRight) => fromBool(toBool(evalLeft) == toBool(evalRight))
            }
        case Eq(left, right) =>
            val jitLeft = compileTerm(left, varIdxs)
            val jitRight = compileTerm(right, varIdxs)
            args => (jitLeft(args) zip jitRight(args)) map {
                case (evalLeft, evalRight) => fromBool(evalLeft == evalRight)
            }
        case IfThenElse(condition, ifTrue, ifFalse) =>
            val jitCondition = compileTerm(condition, varIdxs)
            val jitIfTrue = compileTerm(ifTrue, varIdxs)
            val jitIfFalse = compileTerm(ifFalse, varIdxs)
            args => jitCondition(args) flatMap {
                case Top => jitIfTrue(args)
                case Bottom => jitIfFalse(args)
            }

        // TODO: Evaluate quantifiers by expanding?
        case Forall(_, _) => _ => None
        case Exists(_, _) => _ => None

        // TODO: Evaluate closures. (Currently, run this after closure elimination).
        case Closure(_, _, _, _) => _ => None
        case ReflexiveClosure(_, _, _, _) => _ => None

        // TODO: Evaluate integers and bitvectors and functions of them!
        case IntegerLiteral(_) => _ => None
        case BitVectorLiteral(_, _) => _ => None
        case BuiltinApp(_, _) => _ => None
    }

    // TODO abstract, this is duplicated in Evaluator
    private def toBool(v: Value): Boolean = v match {
        case Top => true
        case Bottom => false
        case _ => Errors.Internal.preconditionFailed("Cannot convert value other than Top, Bottom to Boolean")
    }

    private def fromBool(b: Boolean): Value = if (b) Top else Bottom

}
