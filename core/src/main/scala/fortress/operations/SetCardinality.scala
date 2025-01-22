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
                case Top | Bottom | Var(_) | DomainElement(_, _) | IntegerLiteral(_)
                | BitVectorLiteral(_, _) | EnumValue(_) => term
                case Not(p) => Not(recur(p))
                case AndList(args) => AndList(args map recur)
                case OrList(args) => OrList(args map recur)
                case Distinct(args) => Distinct(args map recur)
                case Iff(left, right) => Iff(recur(left), recur(right))
                case Implication(left, right) => Implication(recur(left), recur(right))
                case Eq(left, right) => Eq(recur(left), recur(right))
                case App(fn, args) => App(fn, args map recur)
                case BuiltinApp(fn, args) => BuiltinApp(fn, args map recur)
                case IfThenElse(c, t, f) => IfThenElse(recur(c), recur(t), recur(f))
                case Forall(vars, body) => Forall(vars, recur(body))
                case Exists(vars, body) => Exists(vars, recur(body))
                
                // addressing warnings, shouldn't have closures by this point
                case Closure(_, _, _, _) => ???
                case ReflexiveClosure(_, _, _, _) => ???

                case SetCardinality(p) => makeCardinalityFunctions(p)
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
