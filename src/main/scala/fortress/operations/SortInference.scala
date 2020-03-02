package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import scala.collection.mutable
import fortress.data._

/** Inferred Type */
sealed abstract class InfSort
case class InfVar(index: Int) extends InfSort
case object InfBool extends InfSort

case class Equation(x: InfSort, y: InfSort)

object SortInference {
    
    type Substitution = Map[Sort, Sort]
    type ContextStack = List[(String, InfSort)]
    
    def inferSorts(theory: Theory): Substitution = {
        /** 
            Booleans don't need to be factored into equation solving.
            Only solve equations between type variables.
        */
        var index = 0
        def freshInt(): Int = {
            val temp = index
            index += 1
            temp
        }
        
        // Associate each constant with an InfSort
        val constantMap: mutable.Map[String, InfSort] = mutable.Map.empty
        for(c <- theory.constants) {
            c.sort match {
                case BoolSort => {constantMap(c.name) = InfBool}
                case SortConst(_) => {constantMap(c.name) = InfVar(freshInt())}
                case _ => ???
            }
        }
        
        // Associate each function with a collection of InfSorts
        val fnMap: mutable.Map[String, (Seq[InfSort], InfSort)] = mutable.Map.empty
        for(f <- theory.functionDeclarations) {
            Errors.precondition(f.argSorts.forall(!_.isBuiltin))
            val args = f.argSorts map (sort => InfVar(freshInt()))
            val result = f.resultSort match {
                case BoolSort => InfBool
                case SortConst(_) => InfVar(freshInt())
                case _ => ???
            }
            fnMap(f.name) = (args, result)
        }
        
        // Gather equations
        
        def lookup(name: String, context: ContextStack): Option[InfSort] = context match {
            case Nil => None
            case (`name`, infsort) :: tail => Some(infsort)
            case _ :: tail => lookup(name, tail)
        }
        
        def recur(term: Term, context: ContextStack): (InfSort, Set[Equation]) = term match {
            case Top => (InfBool, Set.empty)
            case Bottom => (InfBool, Set.empty)
            case Var(name) => lookup(name, context) match {
                case Some(infsort) => (infsort, Set.empty)
                case None => (constantMap(name), Set.empty)
            }
            case EnumValue(_) => ???
            case Not(p) => {
                val (infsort, eqns) = recur(p, context)
                Errors.assertion(infsort == InfBool)
                (InfBool, eqns)
            }
            case AndList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == InfBool))
                val eqns = recurInfo flatMap (_._2)
                (InfBool, eqns.toSet)
            }
            case OrList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == InfBool))
                val eqns = recurInfo flatMap (_._2)
                (InfBool, eqns.toSet)
            }
            case Distinct(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == InfBool))
                val eqns = recurInfo flatMap (_._2)
                (InfBool, eqns.toSet)
            }
            case Implication(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(p, context)
                Errors.assertion(pSort == InfBool)
                Errors.assertion(qSort == InfBool)
                (InfBool, pEqns union qEqns)
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(p, context)
                Errors.assertion(pSort == InfBool)
                Errors.assertion(qSort == InfBool)
                (InfBool, pEqns union qEqns)
            }
            case Eq(l, r) => {
                val (lSort, lEqns) = recur(l, context)
                val (rSort, rEqns) = recur(r, context)
                Errors.assertion(lSort != InfBool)
                Errors.assertion(rSort != InfBool)
                // Add this to equations!
                (InfBool, (lEqns union rEqns) + Equation(lSort, rSort) )
            }
            case App(name, args) => {
                val (argSorts, resSort) = fnMap(name)
                Errors.assertion(argSorts.size == args.size)
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                
                // Add to equations that the argument sorts must match up
                val newEqns = for((sort1, sort2) <- argSorts zip recurArgSorts)
                    yield Equation(sort1, sort2)
                
                val eqns = (recurEqns ++ newEqns).toSet
                (resSort, eqns)
            }
            case Exists(avars, body) => {
                // Give the annotated vars fresh variables
                val freshVars: List[(String, InfSort)] =
                    (avars map {av => (av.name, InfVar(freshInt()))}).toList
                // Must put variables on context stack in reverse
                // e.g. (forall v: A v: B, p(v)), the context should be
                // List[v: B, v: A]
                val newContext = freshVars.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.precondition(bodySort == InfBool)
                (InfBool, bodyEqns)
            }
            case Forall(avars, body) => {
                // Give the annotated vars fresh variables
                val freshVars: List[(String, InfSort)] =
                    (avars map {av => (av.name, InfVar(freshInt()))}).toList
                // Must put variables on context stack in reverse
                // e.g. (forall v: A v: B, p(v)), the context should be
                // List[v: B, v: A]
                val newContext = freshVars.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.precondition(bodySort == InfBool)
                (InfBool, bodyEqns)
            }
            case DomainElement(_, _) => ???
            case BuiltinApp(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
        }
        
        val recurInfo = theory.axioms map {recur(_, Nil)}
        val recurSorts = recurInfo map (_._1)
        Errors.assertion(recurSorts forall (_ == InfBool))
        val recurEqns = (recurInfo flatMap (_._2)).toList
        
        // Solve Equations
        val unionFind = new SimpleUnionFind
        
        ???
    }
    
}
