package fortress.operations
import fortress.msfol._

import fortress.data.IntSuffixNameGenerator
import scala.collection.mutable.Map

import fortress.operations.TermOps._

import fortress.operations.TermOps._
import fortress.util.Errors

object SetCardinalityOperation {

    case class cardinalityResult(cardinalityTerm: Term, inApp_function_names: Map[String, String], cardApp_function_names: Map[String, String])

    def cardinality(term: Term, inApp_function_names: Map[String, String], cardApp_function_names: Map[String, String], nameGenerator: IntSuffixNameGenerator): cardinalityResult = {

        def recur(term: Term): Term = {
            term match {
                case Top | Bottom => term
                case Not(Top) => Bottom
                case Not(Bottom) => Top
                case Not(Not(p)) => recur(p)
                case AndList(args) => AndList(args.map(recur))
                case Not(AndList(args)) => OrList(args.map(arg => recur(Not(arg))))
                case OrList(args) => OrList(args.map(recur))
                case Not(OrList(args)) => AndList(args.map(arg => recur(Not(arg))))
                case Implication(p, q) => OrList(recur(Not(p)), recur(q))
                case Not(Implication(p, q)) => AndList(recur(p), recur(Not(q)))
                case Eq(left, right) => Eq(recur(left), recur(right))
                case Iff(p, q) => OrList(
                    AndList(recur(p), recur(q)),
                    AndList(recur(Not(p)), recur(Not(q)))
                )
                case Not(Iff(p, q)) => OrList(
                    AndList(recur(p), recur(Not(q))),
                    AndList(recur((Not(p))), recur(q))
                )
                case Forall(vars, body) => Forall(vars, recur(body))
                case Not(Forall(vars, body)) => Exists(vars, recur(Not(body)))
                case Exists(vars, body) => Exists(vars, recur(body))
                case Not(Exists(vars, body)) => Forall(vars, recur(Not(body)))
                case (distinct: Distinct) => recur(distinct.asPairwiseNotEquals)
                case Not(distinct @ Distinct(_)) => recur(Not(distinct.asPairwiseNotEquals))
                case IfThenElse(condition, ifTrue, ifFalse) =>
                    IfThenElse(recur(condition), recur(ifTrue), recur(ifFalse))
                case Not(IfThenElse(condition, ifTrue, ifFalse)) =>
                    IfThenElse(recur(condition), recur(Not(ifTrue)), recur(Not(ifFalse)))
                case Not(p) => Not(recur(p))
                case SetCardinality(p) => makeCardinalityFunctions(p)
                
                /* recur makes no changes other term types  */
                case _ => term
        }
        }
        def makeCardinalityFunctions(p : String): Term = {
            if (!cardApp_function_names.contains(p)) {
                // generate functions if need be
                // replace current term with appropriate cardinality name
                val inP_name = nameGenerator.freshName("inP")
                val cardP_name = nameGenerator.freshName("cardP")
                inApp_function_names.put(p, inP_name)
                cardApp_function_names.put(p, cardP_name)
            }
            
            return Var(cardApp_function_names(p)) 
        }
        
        // return replaced term + needed function names
        var cardinalityTerm = recur(term)
        cardinalityResult(cardinalityTerm, inApp_function_names, cardApp_function_names)
    }
}
