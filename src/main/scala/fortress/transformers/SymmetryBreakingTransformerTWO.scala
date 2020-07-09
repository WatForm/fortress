package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.modelfind.ProblemState

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/
class SymmetryBreakingTransformerTWO extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            val breaker = new SymmetryBreaker(theory, scopes)
            
            breaker.breakConstants()
            
            // Only perform symmetry breaking on functions that don't consume or produce
            // builtin types (this also filters out predicates)
            val functions = theory.functionDeclarations filter { fn => {
                (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
            }}
            for(f <- functions) {
                breaker.breakFunction(f)
            }
            
            // Filter function declarations to take only the predicates
            // Additionally, do not take predicates that operate on builtin sorts 
            val predicates = theory.functionDeclarations.filter { fn => {
                (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
            }}
            for(P <- predicates) {
                breaker.breakPredicate(P)
            }
            
            // Comparison operation for functions to determine which order
            // to perform symmetry breaking
            // def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            //     // Lowest arity, then largest # of unused result values
            //     if (f1.arity < f2.arity) true
            //     else if (f1.arity > f2.arity) false
            //     else (tracker.numUnusedDomainElements(f1.resultSort)
            //         > tracker.numUnusedDomainElements(f2.resultSort))
            // }
            
            // Need to update over time
            // def nextFuncOrPred(): Unit = ???
             
            // After functions, do the predicates
            
            // Comparison operation for functions to determine which order
            // to perform symmetry breaking
            // def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
            //     // Lowest arity
            //     P1.arity < P2.arity
            // }
            
            val newTheory = theory.withAxioms(breaker.constraints.toList)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union breaker.newRangeRestrictions.toSet, unapplyInterp)
        }
    }
    
    val name: String = "Symmetry Breaking Transformer - TWO" 
}
