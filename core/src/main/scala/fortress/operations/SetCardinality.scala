package fortress.operations
import fortress.data.NameGenerator

import fortress.msfol._

object SetCardinality {

    case class cardinalityResult(cardinalityTerm: Term, cardinalityFunctions: Set[FuncDecl])

    // how to pass needed names from axiom to axiom? Sets or pass in pass out
    def cardinality(term: Term): cardinalityResult = {
        val inApp_function_names: mutable.Map[String, String] = mutable.Map()
        val cardApp_function_names: mutable.Map[String, String] = mutable.Map()

        def recur(term: Term){
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

            // if I did SetCardinality right, p MUST be a predicate, so p can be used in our first function
            // p( ) **!!! how you do it <<
            // p is a predicate from f to bool, so our scope we care about is f
            case SetCardinality(p) => makeCardinalityFunctions(p)
            
            /* recur makes no changes other term types  */
            case _ => term
            
            
            // here we make definitions based on p
            // we because we found a set cardinality, we know we definitions for inP and cardP
            // bc cardP = Findp(all elements in A)
            // Findp = ite(inA(a), 1, 0)
            //is this the only case that matters?
            
            
            // bookmark, want to use this with sort f
            // need to find the scope of f, which is in the problem state
            // 0 or 1? Question tbd
            // DomainElement(0, f), DomainElement(1, f), DomainElement(2, f), .. , DomainElement(scope, f)
            // scope is just a number         
        }
        
        def makeCardinalityFunctions(p : App): Term {
            if (!cardApp_function_names.contains(p.name)) {
                // generate functions if need be
                // replace current term with appropriate cardinality name
                 name = /* NAME GENERATOR HERE, uses name of predicate ideally */
                inApp_function_names.put(p.name, "in" + name)
                cardApp_function_names.put(p.name, "card" + name) // replace string use with string generator. Don't want to hardcode the strings
            }
            
            return Var(cardApp_function_names.get(term)) 
        }
        
        var cardinalityTerm = recur(term)
        cardinalityResult(cardinalityTerm, inApp_function_names, cardApp_function_names)
    }
}
//     // we potentially want something like this?
//     // def getFixedSorts(fname: String): Seq[Sort] = signature.queryFunction(fname) match {
//     //     case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when closing over it!")
//     //     case Some(Left(FuncDecl(_, sorts, _))) => sorts.drop(2).toList
//     //     case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort).drop(2).toList
//     // }

//     // def ite(term: Term): Term {
//     //     return IfThenElse(term, 1, 0)
//     // }

//     // def removeCardinality(term: Term): Term{
//     //     term match {
//     //         case SetCardinality(term) => SumList (
//     //             ite(term) for term in something
//     //         )
//     //         case _ => term

//     //     }
//     // }

// KIND OF SEPERATE IDEA - we may have multiple instances of the same term, so we don't want to create a new function every time (ex. cardP1, cardP2, etc.) insetad we want to see P and replace with cardP every time.
// Aka we probably want to just replace with the appropriate function name
// Maybe want to do a dictionary type thing? If p has been encounetered use the name names[p], otherwise we generate a new name and add it to the dictionary

/*
// potentially useful - Seq(x,y).map(_.of(sort))
            
            // we need to DECLARE the function (funcdecl) and DEFINE the function seperately
            val body1 = IfThenElse(p(x), 1, 0)
            FunctionDefinition(name, variable, body) // todo, need to get the scope of f (p: f->Bool) and pass that to the function
            val function1= FuncDecl(...) // inP: ite(inA(a), 1, 0) 1 argument, a
            cardinalityFunctions += function1
            
            val body2 = y(DomainElement(0, f)) + y(DomainElement(0, f)) + .... 
            // where y = function we just defined, we will know the namne of y based on p #(p) -> this function
            
            val function2 = FuncDecl(...) // cardP: inp(a1) SUM inp(a2) SUM inp(a3) etc (for all ax in A) // does not take any arguments, applies the first function to all domain elements
            ardinalityFunctions += function2
            function2 // this is the term we want to replace #(p) with
            
            // #
            
            
            // Type - type of argument to the cardinality operator
            // #(P) - p has a sort f-> bool
            // sort I want for ina -> f
            // inA is an application, inA is an app for the argument a
            // where does ina come from? comes from portus, not gauranteed to exist in fortress
            // how do I know what to enumerate ina over? all the domain elements in the sort f
                // class called domainElement
*/