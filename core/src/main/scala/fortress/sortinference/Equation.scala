package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors

case class Equation(x: Sort, y: Sort)

object Equation {

    // Accumulates equations between sort variables
    // Does not accumulate equations for builtin types like Bool, Int, BitVector etc.
    def accumulate(
        constantMap: Map[String, Sort],
        functionMap: Map[String, (Seq[Sort], Sort)],
        formulas: Set[Term] // We assume the input formulas must be sorted as Bool (we add these equations)
    ): Set[Equation] = {

        type ContextStack = List[AnnotatedVar]

        // Lookup the sort of a variable based on the current context
        def lookup(name: String, context: ContextStack): Option[Sort] = context match {
            case Nil => None
            case AnnotatedVar(Var(`name`), sort) :: tail => Some(sort)
            case _ :: tail => lookup(name, tail)
        }
        
        // Returns the sort of the term, and the set of equations that unify it
        def recur(term: Term, context: ContextStack): (Sort, Set[Equation]) = term match {
            case Top | Bottom => (BoolSort, Set.empty)
            case Var(name) => lookup(name, context) match {
                case Some(sort) => (sort, Set.empty)
                case None => (constantMap(name), Set.empty)
            }
            case Not(p) => {
                val (pSort, eqns) = recur(p, context)
                // (BoolSort, eqns + Equation(pSort, BoolSort))
                (BoolSort, eqns)
            }
            case AndList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.Internal.assertion(recurInfo forall (_._1 == BoolSort))
                val recurSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                // // Each argument must be a boolean
                // val boolEqns = recurSorts map (Equation(_, BoolSort))
                // (BoolSort, recurEqns.toSet ++ boolEqns)
                (BoolSort, recurEqns.toSet)
            }
            case OrList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.Internal.assertion(recurInfo forall (_._1 == BoolSort))
                val recurSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                // // Each argument must be a boolean
                // val boolEqns = recurSorts map (Equation(_, BoolSort))
                // (BoolSort, recurEqns.toSet ++ boolEqns)
                (BoolSort, recurEqns.toSet)
            }
            case Distinct(args) => {
                val recurInfo = args map {recur(_, context)}
                // All must be the same sort
                val newEqns: Seq[Option[Equation]] = for(sort <- recurInfo.map(_._1)) yield sort match {
                    case s: SortConst => Some(Equation(recurInfo.head._1, s))
                    case _ => None
                }
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, (eqns ++ newEqns.flatten).toSet)
            }
            case Implication(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                // (BoolSort, pEqns union qEqns + Equation(pSort, BoolSort) + Equation(qSort, BoolSort))
                (BoolSort, pEqns union qEqns)
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                // (BoolSort, pEqns union qEqns + Equation(pSort, BoolSort) + Equation(qSort, BoolSort))
                (BoolSort, pEqns union qEqns)
            }
            case Eq(l, r) => {
                val (lSort, lEqns) = recur(l, context)
                val (rSort, rEqns) = recur(r, context)
                Errors.Internal.assertion(lSort != BoolSort)
                Errors.Internal.assertion(rSort != BoolSort)
                val newEqn: Option[Equation] = (lSort, rSort) match {
                    case (l: SortConst, r: SortConst) => Some(Equation(l, r))
                    case (l, r) => {
                        // Should be equal builtin sorts
                        Errors.Internal.assertion(l == r)
                        None
                    }
                }
                // Add this to equations!
                (BoolSort, (lEqns union rEqns) ++ newEqn)
            }
            case App(name, args) => {
                Errors.Internal.assertion(functionMap.contains(name),name+" not in functionMap")
                val (argSorts, resSort) = functionMap(name)
                Errors.Internal.assertion(argSorts.size == args.size)
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                
                // Add to equations that the argument sorts must match up
                val newEqns: Seq[Option[Equation]] = for {
                    (sort1, sort2) <- argSorts zip recurArgSorts
                } yield (sort1, sort2) match {
                    case (s1: SortConst, s2: SortConst) => Some(Equation(sort1, sort2))
                    case (s1, s2) => {
                        // Should be equal builtin sorts
                        Errors.Internal.assertion(s1 == s2)
                        None
                    }
                } 
                
                val eqns = (recurEqns ++ newEqns.flatten).toSet
                (resSort, eqns)
            }
            case Exists(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                // (BoolSort, bodyEqns + Equation(bodySort, BoolSort))
                (BoolSort, bodyEqns)
            }
            case Forall(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                // (BoolSort, bodyEqns + Equation(bodySort, BoolSort))
                (BoolSort, bodyEqns)
            }
            case DomainElement(index, sort) => {
                (sort, Set.empty)
            }
            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (condSort, condEqns) = recur(condition, context)
                val (ifTrueSort, ifTrueEqns) = recur(ifTrue, context)
                val (ifFalseSort, ifFalseEqns) = recur(ifFalse, context)
                val bothBranchesSameEqn = (ifTrueSort, ifFalseSort) match {
                    case (l: SortConst, r: SortConst) => Some(Equation(l, r))
                    case (s1, s2) => {
                        // Should be equal builtin sorts
                        Errors.Internal.assertion(s1 == s2)
                        None
                    }
                }
                Errors.Internal.assertion(ifTrueSort != BoolSort)
                Errors.Internal.assertion(ifFalseSort != BoolSort)
                // (ifTrueSort, condEqns union ifTrueEqns union ifFalseEqns + Equation(condSort, BoolSort) + Equation(ifTrueSort, ifFalseSort))
                (ifTrueSort, condEqns union ifTrueEqns union ifFalseEqns ++ bothBranchesSameEqn)
            }
            case EnumValue(_) => ???
            case IntegerLiteral(_) => (IntSort, Set.empty)
            case BitVectorLiteral(value, bitwidth) => (BitVectorSort(bitwidth), Set.empty)
            case BuiltinApp(fn, args) => {
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                fn.resultSortFromArgSorts(recurArgSorts) match {
                    case None => Errors.Internal.preconditionFailed("Input formula is not well-typed")
                    case Some(r) => (r, recurEqns.toSet)
                }
            }
            // case BuiltinApp(fn: UnaryIntegerFunction, args) => {
            //     val recurInfo = args map {recur(_, context)}
            //     val recurArgSorts = recurInfo map (_._1)
            //     val recurEqns = recurInfo flatMap (_._2)

            //     // Add to equations that the argument sorts must be Int
            //     val newEqns: Seq[Equation] =
            //         for(argSort <- recurArgSorts)
            //         yield Equation(argSort, IntSort)
                
            //     (IntSort, (recurEqns ++ newEqns).toSet)
            // }
            // case BuiltinApp(fn: BinaryIntegerFunction, args) => {
            //     val recurInfo = args map {recur(_, context)}
            //     val recurArgSorts = recurInfo map (_._1)
            //     val recurEqns = recurInfo flatMap (_._2)

            //     // Add to equations that the argument sorts must be Int
            //     val newEqns: Seq[Equation] =
            //         for(argSort <- recurArgSorts)
            //         yield Equation(argSort, IntSort)
                
            //     (IntSort, (recurEqns ++ newEqns).toSet)
            // }
            // case BuiltinApp(fn: BinaryIntegerRelation, args) => {
            //     val recurInfo = args map {recur(_, context)}
            //     val recurArgSorts = recurInfo map (_._1)
            //     val recurEqns = recurInfo flatMap (_._2)

            //     // Add to equations that the argument sorts must be Int
            //     val newEqns: Seq[Equation] =
            //         for(argSort <- recurArgSorts)
            //         yield Equation(argSort, IntSort)
                
            //     (BoolSort, (recurEqns ++ newEqns).toSet)
            // }
            // Unclear how to support bitvector functions when we don't know the bitwidth
            // May just have to look at arguments and see if any of them give the bitwidth:
            // if so, then that is the bitwidth we must use
            // otherwise, say inference is not possible
            // case BuiltinApp(fn: UnaryBitVectorFunction, _) => ???
            // case BuiltinApp(fn: BinaryBitVectorFunction, _) => ???
            // case BuiltinApp(fn: BinaryBitVectorRelation, _) => ???
        }
        
        val recurInfo = formulas map {recur(_, List.empty)}
        val recurSorts = recurInfo map (_._1)
        val equations = (recurInfo flatMap (_._2))
        // Add equations saying that all formulas must be boolean
        val formulaEquations = recurSorts.map(Equation(_, BoolSort))
        equations ++ formulaEquations.toSet
    }

    type SortVar = SortConst

    // Solve a set of sort equations, using the most general solution 
    def unify(equations: List[Equation]): SortSubstitution = equations match {
        case Nil => SortSubstitution.identity
        case eqn :: eqns => eqn match {
            case Equation(s, t) if s == t => unify(eqns)
            case Equation(x: SortVar, t) => {
                val x_to_t = SortSubstitution.singleton(x -> t)
                unify(eqns map (x_to_t(_))) compose x_to_t
            }
            case Equation(s, x: SortVar) => {
                val x_to_s = SortSubstitution.singleton(x -> s)
                unify(eqns map (x_to_s(_))) compose x_to_s
            }
            case _ => {
                ???
            }
        } 
    }

}