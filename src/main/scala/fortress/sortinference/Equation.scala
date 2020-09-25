package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors

case class Equation(x: Sort, y: Sort)

object Equation {

    def accumulate(
        constantMap: Map[String, Sort],
        functionMap: Map[String, (Seq[Sort], Sort)],
        formulas: Set[Term]
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
            case Top => (BoolSort, Set.empty)
            case Bottom => (BoolSort, Set.empty)
            case Var(name) => lookup(name, context) match {
                case Some(sort) => (sort, Set.empty)
                case None => (constantMap(name), Set.empty)
            }
            case Not(p) => {
                val (sort, eqns) = recur(p, context)
                Errors.assertion(sort == BoolSort)
                (BoolSort, eqns)
            }
            case AndList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == BoolSort))
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, eqns.toSet)
            }
            case OrList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == BoolSort))
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, eqns.toSet)
            }
            case Distinct(args) => {
                val recurInfo = args map {recur(_, context)}
                // All must be the same sort
                val newEqns = for(sort <- recurInfo.map(_._1)) yield Equation(recurInfo.head._1, sort)
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, (eqns ++ newEqns).toSet)
            }
            case Implication(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                Errors.assertion(pSort == BoolSort)
                Errors.assertion(qSort == BoolSort)
                (BoolSort, pEqns union qEqns)
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                Errors.assertion(pSort == BoolSort)
                Errors.assertion(qSort == BoolSort)
                (BoolSort, pEqns union qEqns)
            }
            case Eq(l, r) => {
                val (lSort, lEqns) = recur(l, context)
                val (rSort, rEqns) = recur(r, context)
                Errors.assertion(lSort != BoolSort)
                Errors.assertion(rSort != BoolSort)
                // Add this to equations!
                (BoolSort, (lEqns union rEqns) + Equation(lSort, rSort) )
            }
            case App(name, args) => {
                val (argSorts, resSort) = functionMap(name)
                Errors.assertion(argSorts.size == args.size)
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                
                // Add to equations that the argument sorts must match up
                val newEqns: Seq[Option[Equation]] = {
                    for((sort1, sort2) <- argSorts zip recurArgSorts)
                    yield { 
                        (sort1, sort2) match {
                            case (s1: SortConst, s2: SortConst) => Some(Equation(s1, s2))
                            case (BoolSort, BoolSort) => None
                            case _ => {
                                Errors.assertion(false)
                                ???
                            }
                        }
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
                Errors.assertion(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case Forall(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.assertion(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case EnumValue(_) => ???
            case DomainElement(_, _) => ???
            case BuiltinApp(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (condSort, condEqns) = recur(condition, context)
                val (ifTrueSort, ifTrueEqns) = recur(ifTrue, context)
                val (ifFalseSort, ifFalseEqns) = recur(ifFalse, context)
                Errors.assertion(condSort == BoolSort)
                Errors.assertion(ifTrueSort != BoolSort)
                Errors.assertion(ifFalseSort != BoolSort)
                (ifTrueSort, (condEqns union ifTrueEqns union ifFalseEqns) + Equation(ifTrueSort, ifFalseSort))
            }
        }
        
        val recurInfo = formulas map {recur(_, List.empty)}
        val recurSorts = recurInfo map (_._1)
        Errors.assertion(recurSorts forall (_ == BoolSort))
        val equations = (recurInfo flatMap (_._2))
        equations
    }
}