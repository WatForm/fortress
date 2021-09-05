package fortress.util

import fortress.msfol._
import fortress.data._

class ArgumentListGenerator(scopes: PartialFunction[Sort, Int], sortInterpretations: Option[Map[Sort, Seq[Value]]] = None) {
    
    /** Given a function f: A_1 x ... x A_n -> B, returns an iterable object containing
    all the possible argument combination to the functions. Each argument combination is given as
    a list. For now this only works with functions of uninterpreted sorts. */
    def allArgumentListsOfFunction(f: FuncDecl): Iterable[Seq[Value]] = {
        //  f: A_1 x ... x A_n -> B
        // and each A_i has generated domain D_i
        // get the list [D_1, ..., D_n]
        val seqOfDomainSeqs: IndexedSeq[IndexedSeq[Value]] = f.argSorts.toIndexedSeq.map (sort => sort match {
            case SortConst(s) => {
                if(sortInterpretations.nonEmpty && sortInterpretations.get.contains(sort)){
                    sortInterpretations.get(sort).toIndexedSeq
                } else{
                    DomainElement.range(1 to scopes(sort), sort)
                }
            }
            case BoolSort => Vector(Top, Bottom)
            case _ => ???
        })
        
        // Take the product D_1 x ... x D_n
        val argumentLists: Iterable[Seq[Value]] = new CartesianSeqProduct[Value](seqOfDomainSeqs)
        
        argumentLists
    }
    
}

object ArgumentListGenerator {
    def generate(f: FuncDecl, scopes: PartialFunction[Sort, Int], sortInterpretations: Option[Map[Sort, Seq[Value]]] = None): Iterable[Seq[Value]] = {
        (new ArgumentListGenerator(scopes, sortInterpretations)).allArgumentListsOfFunction(f)
    }
}
