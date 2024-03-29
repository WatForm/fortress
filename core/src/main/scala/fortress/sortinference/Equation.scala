package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors

case class Equation(x: Sort, y: Sort)

object Equation {

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
                (BoolSort, eqns + Equation(pSort, BoolSort))
            }
            case AndList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.Internal.assertion(recurInfo forall (_._1 == BoolSort))
                val recurSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                // Each argument must be a boolean
                val boolEqns = recurSorts map (Equation(_, BoolSort))
                (BoolSort, recurEqns.toSet ++ boolEqns)
            }
            case OrList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.Internal.assertion(recurInfo forall (_._1 == BoolSort))
                val recurSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                // Each argument must be a boolean
                val boolEqns = recurSorts map (Equation(_, BoolSort))
                (BoolSort, recurEqns.toSet ++ boolEqns)
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
                (BoolSort, pEqns union qEqns + Equation(pSort, BoolSort) + Equation(qSort, BoolSort))
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                (BoolSort, pEqns union qEqns + Equation(pSort, BoolSort) + Equation(qSort, BoolSort))
            }
            case Eq(l, r) => {
                val (lSort, lEqns) = recur(l, context)
                val (rSort, rEqns) = recur(r, context)
                Errors.Internal.assertion(lSort != BoolSort)
                Errors.Internal.assertion(rSort != BoolSort)
                // Add this to equations!
                (BoolSort, (lEqns union rEqns) + Equation(lSort, rSort) )
            }
            case App(name, args) => {
                val (argSorts, resSort) = functionMap(name)
                Errors.Internal.assertion(argSorts.size == args.size)
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                
                // Add to equations that the argument sorts must match up
                val newEqns: Seq[Equation] =
                    for((sort1, sort2) <- argSorts zip recurArgSorts)
                    yield Equation(sort1, sort2)
                
                val eqns = (recurEqns ++ newEqns).toSet
                (resSort, eqns)
            }
            case Exists(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                (BoolSort, bodyEqns + Equation(bodySort, BoolSort))
            }
            case Forall(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                (BoolSort, bodyEqns + Equation(bodySort, BoolSort))
            }
            case DomainElement(index, sort) => {
                (sort, Set.empty)
            }
            case BuiltinApp(fn: UnaryIntegerFunction, args) => {
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)

                // Add to equations that the argument sorts must be Int
                val newEqns: Seq[Equation] =
                    for(argSort <- recurArgSorts)
                    yield Equation(argSort, IntSort)
                
                (IntSort, (recurEqns ++ newEqns).toSet)
            }
            case BuiltinApp(fn: BinaryIntegerFunction, args) => {
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)

                // Add to equations that the argument sorts must be Int
                val newEqns: Seq[Equation] =
                    for(argSort <- recurArgSorts)
                    yield Equation(argSort, IntSort)
                
                (IntSort, (recurEqns ++ newEqns).toSet)
            }
            case BuiltinApp(fn: BinaryIntegerRelation, args) => {
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)

                // Add to equations that the argument sorts must be Int
                val newEqns: Seq[Equation] =
                    for(argSort <- recurArgSorts)
                    yield Equation(argSort, IntSort)
                
                (BoolSort, (recurEqns ++ newEqns).toSet)
            }
            case IntegerLiteral(_) => (IntSort, Set.empty)
            case BitVectorLiteral(value, bitwidth) => (BitVectorSort(bitwidth), Set.empty)
            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (condSort, condEqns) = recur(condition, context)
                val (ifTrueSort, ifTrueEqns) = recur(ifTrue, context)
                val (ifFalseSort, ifFalseEqns) = recur(ifFalse, context)
                Errors.Internal.assertion(ifTrueSort != BoolSort)
                Errors.Internal.assertion(ifFalseSort != BoolSort)
                (ifTrueSort, condEqns union ifTrueEqns union ifFalseEqns + Equation(condSort, BoolSort) + Equation(ifTrueSort, ifFalseSort))
            }
            case EnumValue(_) => ???
            // Unclear how to support bitvector functions when we don't know the bitwidth
            // May just have to look at arguments and see if any of them give the bitwidth:
            // if so, then that is the bitwidth we must use
            // otherwise, say inference is not possible
            case BuiltinApp(fn: UnaryBitVectorFunction, _) => ???
            case BuiltinApp(fn: BinaryBitVectorFunction, _) => ???
            case BuiltinApp(fn: BinaryBitVectorRelation, _) => ???
        }
        
        val recurInfo = formulas map {recur(_, List.empty)}
        val recurSorts = recurInfo map (_._1)
        val equations = (recurInfo flatMap (_._2))
        // Add equations saying that all formulas must be boolean
        val formulaEquations = recurSorts.map(Equation(_, BoolSort))
        equations ++ formulaEquations.toSet
    }
}