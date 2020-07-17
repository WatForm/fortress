package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

trait SelectionHeuristic {
    // Select the next function or predicate
    def nextFunctionPredicate(
        usedDomainElements: Map[Sort, Set[DomainElement]],
        remaining: Set[FuncDecl]
    ): Option[FuncDecl]
    
    def acceptableFunction(fn: FuncDecl): Boolean =
        (fn.argSorts :+ fn.resultSort) forall (!_.isBuiltin)
        
    def acceptablePredicate(p: FuncDecl): Boolean =
        (p.argSorts forall (!_.isBuiltin)) && (p.resultSort == BoolSort)
}

object FunctionsFirstAnyOrder extends SelectionHeuristic {
    override def nextFunctionPredicate(
        usedDomainElements: Map[Sort, Set[DomainElement]],
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining find acceptableFunction) orElse (remaining find acceptablePredicate)
    }
}
