package fortress.operations

import fortress.msfol._
import fortress.util.Errors

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
        // TODO: change jit's theory here?
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
        case Iff(left, right) =>
            // Short-circuit: if left is unknown, don't evaluate right
            tryCastToValue(left) flatMap { leftValue =>
                tryCastToValue(right) map { rightValue =>
                    fromBool(toBool(leftValue) == toBool(rightValue))
                }
            }
        case Eq(left, right) =>
            // Short-circuit: if left is unknown, don't evaluate right
            tryCastToValue(left) flatMap { leftValue =>
                tryCastToValue(right) map { rightValue =>
                    fromBool(leftValue == rightValue)
                }
            }
        case IfThenElse(condition, ifTrue, ifFalse) =>
            // Short-circuit: if condition evaluates, don't even evaluate the other branch
            tryCastToValue(condition) flatMap {
                case Top => tryCastToValue(ifTrue)
                case Bottom => tryCastToValue(ifFalse)
            }

        // TODO: Evaluate quantifiers by expanding?
        case Forall(_, _) => None
        case Exists(_, _) => None

        // TODO: Evaluate closures. (Currently, run this after closure elimination).
        case Closure(_, _, _, _) => None
        case ReflexiveClosure(_, _, _, _) => None

        // TODO: Evaluate integers and bitvectors and functions of them!
        case IntegerLiteral(_) => None
        case BitVectorLiteral(_, _) => None
        case BuiltinApp(_, _) => None
    }

    private def tryCastToValue(term: Term): Option[Value] = term match {
        case value: Value => Some(value)
        case _ => None
    }

    private def toBool(v: Value): Boolean = v match {
        case Top => true
        case Bottom => false
        case _ => Errors.Internal.preconditionFailed("Cannot convert value other than Top, Bottom to Boolean")
    }

    private def fromBool(b: Boolean): Value = if (b) Top else Bottom

}
