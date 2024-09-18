package fortress.operations

import fortress.msfol._

object SetCardinality {

    case class cardinalityResult(cardinalityTerm: Term, cardinalityFunctions: Set[FuncDecl])

    def cardinality(term: Term): cardinalityResult = {
        
        val cardinalityFunctions = scala.collection.mutable.Set[FuncDecl]()

        def recur(term: Term){
            case _ => term // this may not be enough, may need to traverse the tree by calling recur on the inner terms
            
            case SetCardinality(p) => makeCardinalityFunctions(p)
            // here we make definitions based on p
            // we because we found a set cardinality, we know we definitions for inP and cardP
            // bc cardP = Findp(all elements in A)
            // Findp = ite(inA(a), 1, 0)
            //is this the only case that matters?            
        }
        
        def makeCardinalityFunctions(term: Term): cardinalityResult {
            val function1= FuncDecl(...) // cardp: ite(inA(a), 1, 0)
            cardinalityFunctions += function1
            val function2 = FuncDecl(...) // cardp(a1) SUM cardp(a2) SUM cardp(a3) etc (for all ax in A)
            ardinalityFunctions += function2
            function2 // this is the term we want to replace #(p) with
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