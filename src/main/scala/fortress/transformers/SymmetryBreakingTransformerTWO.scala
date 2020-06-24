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
                val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, scope, usedVals)
                
                // Add to constraints
                constraints ++= constantRangeRestrictions map (_.asFormula)
                newRangeRestrictions ++= constantRangeRestrictions
                constraints ++= constantImplications
                // Add to used values
                tracker.markUsed(constantRangeRestrictions flatMap (_.asFormula.domainElements))
                tracker.markUsed(constantImplications flatMap (_.domainElements))
            }
            
            // After constants, do all of the functions
            
            // Comparison operation for functions to determine which order
            // to perform symmetry breaking
            def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
                // Lowest arity, then largest # of unused result values
                if (f1.arity < f2.arity) true
                else if (f1.arity > f2.arity) false
                else (tracker.numUnusedDomainElements(f1.resultSort)
                    > tracker.numUnusedDomainElements(f2.resultSort))
            }
            
            // Only perform symmetry breaking on functions that don't consume or produce
            // builtin types (this also filters out predicates)
            val functions = theory.functionDeclarations filter { fn => {
                (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
            }}
            
            // Apply symmetry breaking to the functions
            for(f <- functions) {
                val resultSort = f.resultSort
                val scope = scopes(resultSort)
                val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
                
                if(tracker.stillUnusedDomainElements(resultSort)) {
                    if (f.isDomainRangeDistinct) {
                        // DRD scheme
                        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, scopes, usedVals)
                        val fImplications = Symmetry.drdFunctionImplicationsSimplified(f, scopes, usedVals)
                        
                        // Add to constraints
                        constraints ++= fRangeRestrictions map (_.asFormula)
                        newRangeRestrictions ++= fRangeRestrictions
                        constraints ++= fImplications
                        // Add to used values
                        tracker.markUsed(fRangeRestrictions flatMap (_.asFormula.domainElements))
                        tracker.markUsed(fImplications flatMap (_.domainElements))
                        
                    } else {
                        // Extended CS scheme
                        val fRangeRestrictions = Symmetry.csFunctionExtRangeRestrictions(f, scope, usedVals)
                        
                        // Add to constraints
                        constraints ++= fRangeRestrictions map (_.asFormula)
                        newRangeRestrictions ++= fRangeRestrictions
                        // Add to used values
                        tracker.markUsed(fRangeRestrictions flatMap (_.asFormula.domainElements))
                    }
                }
            }
             
            // After functions, do the predicates
            
            // Comparison operation for functions to determine which order
            // to perform symmetry breaking
            def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
                // Lowest arity
                P1.arity < P2.arity
            }
            
            // Filter function declarations to take only the predicates
            // Additionally, do not take predicates that operate on builtin sorts 
            val predicates = theory.functionDeclarations.filter { fn => {
                (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
            }}
            
            // Apply symmetry breaking to the predicates
            for(P <- predicates) {
                if(P.argSorts forall (tracker.numUnusedDomainElements(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
                    val usedValues: Map[Sort, IndexedSeq[DomainElement]] = tracker.usedDomainElements map {
                        case (sort, setOfVals) => (sort, setOfVals.toIndexedSeq)
                    }
                    val pImplications = Symmetry.predicateImplications(P, scopes, usedValues)
                    
                    // Add to constraints
                    constraints ++= pImplications
                    // Add to used values
                    tracker.markUsed(pImplications flatMap (_.domainElements))
                }
            }
            
            val newTheory = theory.withAxioms(constraints.toList)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions.toSet, unapplyInterp)
        }
    }
    
    val name: String = "Symmetry Breaking Transformer - TWO" 
}
