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
            val tracker = new DomainElementTracker(theory, scopes)
            
            // Accumulates the symmetry breaking constraints
            val constraints = new mutable.ListBuffer[Term]
            val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
            
            // Symmetry break on constants first
            for(sort <- theory.sorts if !sort.isBuiltin && tracker.stillUnusedDomainElements(sort)) {
                val constants = theory.constants.filter(_.sort == sort).toIndexedSeq
                val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
                val scope = scopes(sort)
                val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, scope, usedVals)
                val constantImplications = Symmetry.csConstantImplications(sort, constants, scope, usedVals)
                
                // Add to constraints
                constraints ++= constantRangeRestrictions map (_.asFormula)
                newRangeRestrictions ++= constantRangeRestrictions
                constraints ++= constantImplications
                // Add to used values
                tracker.markUsed(constantRangeRestrictions flatMap (_.asFormula.domainElements))
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
                    val fRangeRestrictions = Symmetry.csFunctionExtRangeRestrictions(f, scope, usedVals)
                    
                    // Add to constraints
                    constraints ++= fRangeRestrictions map (_.asFormula)
                    newRangeRestrictions ++= fRangeRestrictions
                    // Add to used values
                    tracker.markUsed(fRangeRestrictions flatMap (_.asFormula.domainElements))
                }
            }
            
            val newTheory = theory.withAxioms(constraints.toList)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions.toSet, unapplyInterp)
        }
    }
    
    val name: String = "Symmetry Breaking Transformer - ONE" 
}
