package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original. This transformer is only for testing purposes:
* SymmetryBreakingTransformerTWO should be used in practice.
*/
class SymmetryBreakingTransformerONE extends ProblemTransformer {
        
    def apply(problem: Problem): Problem = problem match {
        case Problem(theory, scopes) => {
            val tracker = new DomainElementTracker(theory, scopes)
            
            // Accumulates the symmetry breaking constraints
            val constraints = new mutable.ListBuffer[Term]
            
            // Symmetry break on constants first
            for(sort <- theory.sorts if !sort.isBuiltin && tracker.stillUnusedDomainElements(sort)) {
                val constants = theory.constants.filter(_.sort == sort).toIndexedSeq
                val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
                val scope = scopes(sort)
                val constantEqualities = Symmetry.csConstantEqualities(sort, constants, scope, usedVals)
                val constantImplications = Symmetry.csConstantImplications(sort, constants, scope, usedVals)
                
                // Add to constraints
                constraints ++= constantEqualities
                constraints ++= constantImplications
                // Add to used values
                tracker.markUsed(constantEqualities flatMap (_.domainElements))
                tracker.markUsed(constantImplications flatMap (_.domainElements))
            }
            
            // After constants, do functions
            
            // Search for functions of the form f: A x ... x A -> A
            def isAtoA(f: FuncDecl): Boolean = f.argSorts.forall(_ == f.resultSort) && !f.resultSort.isBuiltin
            
            // We don't really care what order we break these functions in
            // Even arity doesn't make a difference, since it all boils
            // down to symmetry breaking a unary function
            for(f <- theory.functionDeclarations if isAtoA(f)) {
                val sort = f.resultSort
                val scope = scopes(sort)
                val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
                if(tracker.stillUnusedDomainElements(sort)) {
                    val fEqualities = Symmetry.csFunctionExtEqualities(f, scope, usedVals)
                    
                    // Add to constraints
                    constraints ++= fEqualities
                    // Add to used values
                    tracker.markUsed(fEqualities flatMap (_.domainElements))
                }
            }
            
            val newTheory = theory.withAxioms(constraints.toList)
            Problem(newTheory, scopes)
        }
    }
    
    val name: String = "Symmetry Breaking Transformer - ONE" 
}
