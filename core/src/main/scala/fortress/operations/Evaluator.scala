package fortress.operations

import fortress.msfol._
import fortress.util.Errors

import scala.collection.mutable

/**
  * Evaluates intepretation-independent terms to values if possible.
  */
class Evaluator(theory: Theory) {

    private val defnCache = mutable.Map[(String, Seq[Option[Value]]), Option[Value]]()

    /** Evaluate the term fully to a value if possible. */
    def evaluate(term: Term): Option[Value] = fullEvaluate(term, Map.empty)

    /** Evaluate the term, but do not recurse through arguments beyond checking whether they are a value. */
    def shallowEvaluate(term: Term): Option[Value] = {
        def tryCastToValue(term: Term): Option[Value] = term match {
            case value: Value => Some(value)
            case _ => None
        }
        doEvaluate(term, Map.empty, tryCastToValue)
    }

    private def fullEvaluate(term: Term, varMap: Map[Var, Option[Value]]): Option[Value] = {
        def subEvaluate(term: Term): Option[Value] = doEvaluate(term, varMap, subEvaluate)
        subEvaluate(term)
    }

    // Get the value that term evaluates to, or None if term is not interpretation-independent.
    // recurse is the function to use for recursing on arguments.
    private def doEvaluate(term: Term, varMap: Map[Var, Option[Value]], recurse: Term => Option[Value]): Option[Value] =
        term match {
        // Value literals
        case Top => Some(Top)
        case Bottom => Some(Bottom)
        case de @ DomainElement(_, _) => Some(de)

        // Special cases
        case v @ Var(_) => varMap.get(v).flatten // if not in varMap, it must be a constant; TODO handle cDefs?
        case App(name, args) => theory.functionDefinitions find (_.name == name) match {
            // We can only evaluate calls to definitions
            case None => None
            // Evaluate each argument and evaluate the body with a new variable context.
            // Note that we still evaluate even if not all of the arguments evaluate; they could be short-circuited out.
            case Some(fDef) =>
                val newArgs = args map recurse
                defnCache.getOrElseUpdate((name, newArgs),
                    fullEvaluate(fDef.body, ((fDef.argSortedVar map (_.variable)) zip newArgs).toMap))
        }

        // Evaluate boolean operations. This corresponds to 3-valued logic with an unknown.
        case Not(p) => recurse(p) map {
            case Top => Bottom
            case Bottom => Top
        }
        case AndList(args) =>
            def reduceAnd(args: Seq[Term]): Option[Value] = args match {
                // Reduce with short-circuiting: don't even evaluate if we've short-circuited
                case Seq() => Some(Top)
                case head +: tail => recurse(head) match {
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
                case head +: tail => recurse(head) match {
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
                case head +: tail => recurse(head) match {
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
            recurse(left) flatMap {
                case Top => recurse(right)
                case Bottom => Some(Top) // (false => x) == true for all x
            }
        case Iff(left, right) => (recurse(left) zip recurse(right)) map {
            case (a, b) => fromBool(toBool(a) == toBool(b))
        }
        case Eq(left, right) => (recurse(left) zip recurse(right)) map {
            case (a, b) => fromBool(a == b)
        }
        case IfThenElse(condition, ifTrue, ifFalse) =>
            // Short-circuit: if condition evaluates, don't even evaluate the other branch
            recurse(condition) flatMap {
                case Top => recurse(ifTrue)
                case Bottom => recurse(ifFalse)
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

    private def toBool(v: Value): Boolean = v match {
        case Top => true
        case Bottom => false
        case _ => Errors.Internal.preconditionFailed("Cannot convert value other than Top, Bottom to Boolean")
    }

    private def fromBool(b: Boolean): Value = if (b) Top else Bottom

}
