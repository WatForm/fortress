package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.operations._

trait SelectionHeuristic {
    
    def name: String
    
    // Select the next function or predicate
    def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl]
    
    protected def acceptableFunction(fn: FuncDecl): Boolean =
        (fn.argSorts :+ fn.resultSort) forall (!_.isBuiltin)
        
    protected def acceptablePredicate(p: FuncDecl): Boolean =
        (p.argSorts forall (!_.isBuiltin)) && (p.resultSort == BoolSort)
}

object FunctionsFirstAnyOrder extends SelectionHeuristic {
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining find acceptableFunction) orElse (remaining find acceptablePredicate)
    }
    
    override def name = "Functions First, Any Order"
}

object PredicatesFirstAnyOrder extends SelectionHeuristic {
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining find acceptablePredicate) orElse (remaining find acceptableFunction)
    }
    
    override def name = "Predicates First, Any Order"
}

object FunctionsFirstGreedy extends SelectionHeuristic {
    
    override def name = "Functions First, Greedy"
    
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then largest # of fresh result values
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else (state.numFreshValues(f1.resultSort)
                > state.numFreshValues(f2.resultSort))
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

object PredicatesFirstGreedy extends SelectionHeuristic {
    
    override def name = "Predicates First, Greedy"
    
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then largest # of fresh result values
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else (state.numFreshValues(f1.resultSort)
                > state.numFreshValues(f2.resultSort))
        }
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
            // Lowest arity
            P1.arity < P2.arity
        }
        
        ((remaining filter acceptablePredicate).toSeq sortWith predLessThan).headOption
            .orElse { ((remaining filter acceptableFunction).toSeq sortWith fnLessThan).headOption }
    }
}

object PredicatesOnlyAnyOrder extends SelectionHeuristic {
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        remaining find acceptablePredicate
    }
    
    override def name = "Predicates Only, Any Order"
}

object Random extends SelectionHeuristic {
    
    override def name = "Random"
    
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        val valid = (remaining filter (f => acceptableFunction(f) || acceptablePredicate(f)))
        scala.util.Random.shuffle(valid.toList).headOption
    }
}

object MonoOnlyAnyOrder extends SelectionHeuristic {
    
    override def name = "Mono Only, Any Order"
    
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining filter (_.isMonoSorted)).headOption
    }
}

object MonoFirstThenFunctionsFirstAnyOrder extends SelectionHeuristic {
    
    override def name = "Mono First, then Functions, then Predicates"
    
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
        
        (remaining filter (_.isMonoSorted)).headOption orElse (remaining find acceptableFunction) orElse (remaining find acceptablePredicate)
    }
}

object NoFunctionsPredicates extends SelectionHeuristic {
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = None
    
    override def name = "No Functions or Predicates"
}

// Decorator
class SelectAfterSubstitution(baseSelection: SelectionHeuristic, sortSubstitution: SortSubstitution) extends SelectionHeuristic {
    override def nextFunctionPredicate(
        state: StalenessState,
        remaining: Set[FuncDecl]
    ): Option[FuncDecl] = {
    // Have to change state as well
        val stateSub = state.afterSubstitution(sortSubstitution)
        val remainingSub = remaining map sortSubstitution
        baseSelection.nextFunctionPredicate(stateSub, remainingSub)
    }

    override def name = "Substitution + " + baseSelection.name
}