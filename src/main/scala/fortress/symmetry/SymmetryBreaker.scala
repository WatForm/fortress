package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

import scala.collection.mutable

class SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int]) {
    private val tracker = DomainElementTracker.create(theory, scopes)
    
    // Accumulates the symmetry breaking constraints
    val constraints = new mutable.ListBuffer[Term]
    val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
    
    def breakConstants(): Unit = {
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
    }
    
    def breakFunction(f: FuncDecl): Unit = {
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
    
    def breakPredicate(P: FuncDecl): Unit = {
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
    
    def usedDomainElements: Map[Sort, Set[DomainElement]] = tracker.usedDomainElements
}
