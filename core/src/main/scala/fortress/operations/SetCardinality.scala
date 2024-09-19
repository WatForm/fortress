package fortress.operations

import fortress.msfol._

object SetCardinality {

    case class cardinalityResult(cardinalityTerm: Term, cardinalityFunctions: Set[FuncDecl])

    def cardinality(term: Term): cardinalityResult = {
        
        val cardinalityFunctions = scala.collection.mutable.Set[FuncDecl]()

        def recur(term: Term){
            
            // if I did SetCardinality right, p MUST be a predicate, so p can be used in our first function
            // p( ) **!!! how you do it <<
            // p is a predicate from f to bool, so our scope we care about is f
            case SetCardinality(p) => makeCardinalityFunctions(p)
            case _ => term // this may not be enough, may need to traverse the tree by calling recur on the inner terms
            // this was in fact not enough, traverese down!!!
            
            
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
        
        def makeCardinalityFunctions(p : App): cardinalityResult {
            // KIND OF SEPERATE IDEA - we may have multiple instances of the same term, so we don't want to create a new function every time (ex. cardP1, cardP2, etc.) insetad we want to see P and replace with cardP every time.
            // Aka we probably want to just replace with the appropriate function name
            // Maybe want to do a dictionary type thing? If p has been encounetered use the name names[p], otherwise we generate a new name and add it to the dictionary
            
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
        }
        
        var cardinalityTerm = recur(term)
        cardinalityResult(cardinalityTerm, cardinalityFunctions)
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