package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

trait SelectionHeuristic {
    // Select the next function or predicate
    def nextFunctionPredicate(
        tracker: DomainElementTracker,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl]
    
    def acceptableFunction(fn: FuncDecl): Boolean =
        (fn.argSorts :+ fn.resultSort) forall (!_.isBuiltin)
        
    def acceptablePredicate(p: FuncDecl): Boolean =
        (p.argSorts forall (!_.isBuiltin)) && (p.resultSort == BoolSort)
}

object FunctionsFirstAnyOrder extends SelectionHeuristic {
    override def nextFunctionPredicate(
        tracker: DomainElementTracker,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining find acceptableFunction) orElse (remaining find acceptablePredicate)
    }
}

object FunctionsFirstGreedy extends SelectionHeuristic {
    
    override def nextFunctionPredicate(
        tracker: DomainElementTracker,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then largest # of unused result values
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else (tracker.numUnusedDomainElements(f1.resultSort)
                > tracker.numUnusedDomainElements(f2.resultSort))
        }
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
            // Lowest arity
            P1.arity < P2.arity
        }
        
        ((remaining filter acceptableFunction).toSeq sortWith fnLessThan).headOption
            .orElse { ((remaining filter acceptablePredicate).toSeq sortWith predLessThan).headOption }
    }
}

object Random extends SelectionHeuristic {
    override def nextFunctionPredicate(
        tracker: DomainElementTracker,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        val valid = (remaining filter (f => acceptableFunction(f) || acceptablePredicate(f)))
        scala.util.Random.shuffle(valid.toList).headOption
    }
}
