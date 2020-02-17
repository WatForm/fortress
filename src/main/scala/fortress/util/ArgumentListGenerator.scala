package fortress.util

import fortress.msfol._
import scala.collection.immutable.Seq
import fortress.data._

class ArgumentListGenerator(scopes: Map[Sort, Int]) {
    
    /** Given a function f: A_1 x ... x A_n -> B, returns an iterable object containing
    all the possible argument combination to the functions. Each argument combination is given as
    a list. For now this only works with functions of uninterpreted sorts. */
    def allArgumentListsOfFunction(f: FuncDecl): Iterable[Seq[DomainElement]] = {
        val possibleRangeValues = for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)
        
        //  f: A_1 x ... x A_n -> B
        // and each A_i has generated domain D_i
        // get the list [D_1, ..., D_n]
        var counter = 0
        val seqOfDomainSeqs: IndexedSeq[IndexedSeq[DomainElement]] = f.argSorts.toIndexedSeq.map (sort => {
            val Di: IndexedSeq[DomainElement] = for(j <- 1 to scopes(sort)) yield DomainElement(j, sort)
            Di
        })
        
        // Take the product D_1 x ... x D_n
        val argumentLists: Iterable[Seq[DomainElement]] = new CartesianSeqProduct[DomainElement](seqOfDomainSeqs)
        
        argumentLists
    }
    
}
