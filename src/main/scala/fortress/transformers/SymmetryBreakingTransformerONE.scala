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
* equisatisfiable to the original. This transformer is only for testing purposes:
* SymmetryBreakingTransformerTWO should be used in practice.
*/
class SymmetryBreakingTransformerONE extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            val breaker = new SymmetryBreaker(theory, scopes)
            
            breaker.breakConstants()
            
            // After constants, do functions
            
            // Search for functions of the form f: A x ... x A -> A
            def isAtoA(f: FuncDecl): Boolean = f.argSorts.forall(_ == f.resultSort) && !f.resultSort.isBuiltin
            
            // We don't really care what order we break these functions in
            // Even arity doesn't make a difference, since it all boils
            // down to symmetry breaking a unary function
            for(f <- theory.functionDeclarations if isAtoA(f)) {
                breaker.breakFunction(f)
            }
            
            val newTheory = theory.withAxioms(breaker.constraints.toList)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union breaker.newRangeRestrictions.toSet, unapplyInterp)
        }
    }
    
    val name: String = "Symmetry Breaking Transformer - ONE" 
}
