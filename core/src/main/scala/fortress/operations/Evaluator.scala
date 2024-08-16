package fortress.operations

import fortress.msfol._

/**
  * Evaluates intepretation-independent terms to values if possible.
  */
class Evaluator(private var theory: Theory) {

    private val jit = new DefinitionJit(theory)

    /**
      * Swap the theory without clearing the cache.
      * For use when definition bodies have been simplified but not semantically changed.
      */
    def changeTheory(theory: Theory): Unit = {
        this.theory = theory
    }

    // Get the value that term evaluates to, or None if term is not interpretation-independent.
    // Do not recurse through the terms: instead, look at the term's children as-is.
    def shallowEvaluate(term: Term): Option[Value] = term match {
        // Value literals
        case Top => Some(Top)
        case Bottom => Some(Bottom)
        case de @ DomainElement(_, _) => Some(de)

        // Special cases
        case Var(_) => None // it must be a constant; TODO handle cDefs?
        case App(name, args) => theory.functionDefinitions find (_.name == name) match {
            // We can only evaluate calls to definitions
            case None => None
            // Evaluate each argument and evaluate the body with a new variable context.
            // Note that we still evaluate even if not all of the arguments evaluate; they could be short-circuited out.
            case Some(fDef) =>
                val newArgs = args map tryCastToValue
                jit.evaluate(fDef, newArgs)
        }

        // Evaluate boolean operations. This corresponds to 3-valued logic with an unknown.
        case Not(p) => tryCastToValue(p) map {
            case Top => Bottom
            case Bottom => Top
        }
        case AndList(args) =>
            // TODO: This can be simplified since tryCastToValue is cheap
            def reduceAnd(args: Seq[Term]): Option[Value] = args match {
                // Reduce with short-circuiting: don't even evaluate if we've short-circuited
                case Seq() => Some(Top)
                case head +: tail => tryCastToValue(head) match {
                    case Some(Bottom) => Some(Bottom) // short-circuit: false && x == false for all x
                    case Some(Top) => reduceAnd(tail) // true && x == x for all x
                    case None => reduceAnd(tail) flatMap {
                        case Bottom => Some(Bottom) // unknown && false == false
                        case Top => None // unknown && true == unknown
                    }
                }
            }
            reduceAnd(args)
        case OrList(args) =>
            def reduceOr(args: Seq[Term]): Option[Value] = args match {
                // Reduce with short-circuiting: don't even evaluate if we've short-circuited
                case Seq() => Some(Bottom)
                case head +: tail => tryCastToValue(head) match {
                    case Some(Top) => Some(Top) // short-circuit: true || x == true for all x
                    case Some(Bottom) => reduceOr(tail) // false || x == x for all x
                    case None => reduceOr(tail) flatMap {
                        case Top => Some(Top) // unknown || true == true
                        case Bottom => None // unknown || false == unknown
                    }
                }
            }
            reduceOr(args)
        case Distinct(args) =>
            def reduceDistinct(args: Seq[Term], seen: Set[Value]): Option[Value] = args match {
                // Reduce with short-circuiting again: short-circuit if the evaluated value is already seen
                case Seq() => Some(Top)
                case head +: tail => tryCastToValue(head) match {
                    case Some(value) =>
                        if (seen contains value) Some(Bottom) // short-circuit: two are equal
                        else reduceDistinct(tail, seen + value)
                    case None => reduceDistinct(tail, seen) flatMap {
                        case Bottom => Some(Bottom) // distinct(unknown, *non-distinct) == false
                        case Top => None // distinct(unknown, *distinct) == unknown
                    }
                }
            }
            reduceDistinct(args, Set.empty)
        case Implication(left, right) =>
            // Short-circuit: don't evaluate right if left is unknown or false
            tryCastToValue(left) flatMap {
                case Top => tryCastToValue(right)
                case Bottom => Some(Top) // (false => x) == true for all x
            }
        case Iff(left, right) => evalEqIff(left, right)
        case Eq(left, right) => evalEqIff(left, right)
        case IfThenElse(condition, ifTrue, ifFalse) =>
            // Short-circuit: if condition evaluates, don't even evaluate the other branch
            tryCastToValue(condition) flatMap {
                case Top => tryCastToValue(ifTrue)
                case Bottom => tryCastToValue(ifFalse)
            }

        // Evaluate integers
        case i @ IntegerLiteral(_) => Some(i)
        case BuiltinApp(IntNeg, Seq(x)) => tryCastToValue(x) map {
            case IntegerLiteral(i) => IntegerLiteral(-i)
        }
        case BuiltinApp(IntPlus, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i + j)
        }
        case BuiltinApp(IntSub, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i - j)
        }
        case BuiltinApp(IntMult, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => IntegerLiteral(i * j)
        }
        case BuiltinApp(IntDiv, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) flatMap {
            case (_, IntegerLiteral(0)) => None // don't try and handle div-by-zero here
            case (IntegerLiteral(i), IntegerLiteral(j)) => Some(IntegerLiteral(i / j))
        }
        case BuiltinApp(IntMod, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) flatMap {
            case (_, IntegerLiteral(0)) => None // don't try and handle mod-by-zero here
            case (IntegerLiteral(i), IntegerLiteral(j)) => Some(IntegerLiteral(i % j))
        }
        case BuiltinApp(IntLE, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i <= j)
        }
        case BuiltinApp(IntLT, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i < j)
        }
        case BuiltinApp(IntGE, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i >= j)
        }
        case BuiltinApp(IntGT, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i > j)
        }
        case BuiltinApp(IntEQ, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (IntegerLiteral(i), IntegerLiteral(j)) => fromBool(i == j)
        }

        // Evaluate BitVectors
        case bv @ BitVectorLiteral(_, _) => Some(bv)
        case BuiltinApp(BvNeg, Seq(x)) => tryCastToValue(x) map {
            case BitVectorLiteral(i, bitwidth) => wrapBv(-i, bitwidth)
        }
        case BuiltinApp(BvPlus, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i + j, bw1)
        }
        case BuiltinApp(BvSub, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i - j, bw1)
        }
        case BuiltinApp(BvMult, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => wrapBv(i * j, bw1)
        }
        case BuiltinApp(BvSignedDiv, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) flatMap {
            case (_, BitVectorLiteral(0, _)) => None // don't try and handle div-by-zero here
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => Some(wrapBv(i / j, bw1))
        }
        case BuiltinApp(BvSignedMod, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) flatMap {
            case (_, BitVectorLiteral(0, _)) => None // don't try and handle mod-by-zero here
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 =>
                // In BvSignedMod, the sign follows the divisor (second argument)
                // https://z3prover.github.io/api/html/group__capi.html#ga9f99e96fc60cb67789fab87be0ba5919
                val result = (i.abs % j.abs) * j.sign
                Some(wrapBv(result, bw1))
        }
        case BuiltinApp(BvSignedRem, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) flatMap {
            case (_, BitVectorLiteral(0, _)) => None // don't try and handle rem-by-zero here
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 =>
                // In BvSignedRem, the sign follows the dividend (first argument)
                // https://z3prover.github.io/api/html/group__capi.html#ga9f99e96fc60cb67789fab87be0ba5919
                val result = (i.abs % j.abs) * i.sign
                Some(wrapBv(result, bw1))
        }
        case BuiltinApp(BvSignedLE, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i <= j)
        }
        case BuiltinApp(BvSignedLT, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i < j)
        }
        case BuiltinApp(BvSignedGE, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i >= j)
        }
        case BuiltinApp(BvSignedGT, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i > j)
        }
        case BuiltinApp(BvEQ, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) if bw1 == bw2 => fromBool(i == j)
        }
        case BuiltinApp(BvConcat, Seq(x, y)) => (tryCastToValue(x) zip tryCastToValue(y)) map {
            case (BitVectorLiteral(i, bw1), BitVectorLiteral(j, bw2)) => BitVectorLiteral((i << bw2) | j, bw1 + bw2)
        }

        // TODO: Evaluate quantifiers by expanding?
        case Forall(_, _) => None
        case Exists(_, _) => None

        // TODO: Evaluate closures. (Currently, run this after closure elimination).
        case Closure(_, _, _, _) => None
        case ReflexiveClosure(_, _, _, _) => None
    }

    // Short-circuit: if left is unknown, don't evaluate right
    private def evalEqIff(left: Term, right: Term): Option[Value] = tryCastToValue(left) flatMap { leftValue =>
        tryCastToValue(right) map { rightValue => fromBool(leftValue == rightValue) }
    }

    private def tryCastToValue(term: Term): Option[Value] = term match {
        case value: Value => Some(value)
        case _ => None
    }

    private def fromBool(bool: Boolean): Value = if (bool) Top else Bottom

    private def wrapBv(value: Int, bitwidth: Int): BitVectorLiteral =
        BitVectorLiteral(value & ((1 << bitwidth) - 1), bitwidth)

}
