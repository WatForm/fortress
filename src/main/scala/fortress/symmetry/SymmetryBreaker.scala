package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

import scala.collection.mutable

trait SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker
}

abstract class SymmetryBreaker(
    theory: Theory,
    protected val scopes: Map[Sort, Int]
) {
    
    val tracker = DomainElementTracker.create(theory, scopes)
    
    // Accumulates the symmetry breaking constraints
    val constraints = new mutable.ListBuffer[Term]
    val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
    
    def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit
    def breakFunction(f: FuncDecl): Unit
    def breakPredicate(P: FuncDecl): Unit
    
    def usedDomainElements: Map[Sort, Set[DomainElement]] = tracker.usedDomainElements
    
    protected def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
        // Add to constraints
        constraints ++= rangeRestrictions map (_.asFormula)
        newRangeRestrictions ++= rangeRestrictions
        // Add to used values
        tracker.markUsed(rangeRestrictions flatMap (_.asFormula.domainElements))
    }
    protected def addGeneralConstraints(fmls: Set[Term]): Unit = {
        // Add to constraints
        constraints ++= fmls
        // Add to used values
        tracker.markUsed(fmls flatMap (_.domainElements))
    }
}

trait DefaultPredicateBreaking extends SymmetryBreaker {
    override def breakPredicate(P: FuncDecl): Unit = {
        if(P.argSorts forall (tracker.numUnusedDomainElements(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
            val usedValues: Map[Sort, IndexedSeq[DomainElement]] = tracker.usedDomainElements map {
                case (sort, setOfVals) => (sort, setOfVals.toIndexedSeq)
            }
            val pImplications = Symmetry.predicateImplications(P, scopes, usedValues)
            addGeneralConstraints(pImplications)
        }
    }
}

trait DrdDifferentiation extends SymmetryBreaker {
    def breakDrdFunction(f: FuncDecl): Unit
    def breakNonDrdFunction(f: FuncDecl): Unit
    
    override def breakFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        
        if(tracker.stillUnusedDomainElements(resultSort)) {
            if (f.isDomainRangeDistinct) {
                breakDrdFunction(f)
            } else {
                breakNonDrdFunction(f)
            }
        }
    }
}

trait DefaultNonDrdScheme extends DrdDifferentiation {
    override def breakNonDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // Extended CS scheme
        val fRangeRestrictions = Symmetry.csFunctionExtRangeRestrictions(f, scope, usedVals)
        addRangeRestrictions(fRangeRestrictions)
    }
}

// Concrete Implementations

class DefaultSymmetryBreaker(theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DefaultPredicateBreaking
with DrdDifferentiation
with DefaultNonDrdScheme {
    
    override def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for(sort <- theory.sorts if !sort.isBuiltin && tracker.stillUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
            val scope = scopes(sort)
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, scope, usedVals)
            val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, scope, usedVals)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // DRD scheme
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, scopes, usedVals)
        val fImplications = Symmetry.drdFunctionImplicationsSimplified(f, scopes, usedVals)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
    }
}

object DefaultSymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new DefaultSymmetryBreaker(theory, scopes)
}

// No implications for functions or constants (but still for predicates)
class Imp0SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DefaultPredicateBreaking
with DrdDifferentiation
with DefaultNonDrdScheme {
    
    override def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for(sort <- theory.sorts if !sort.isBuiltin && tracker.stillUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
            val scope = scopes(sort)
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, scope, usedVals)
            // val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, scope, usedVals)
            
            addRangeRestrictions(constantRangeRestrictions)
            // addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // DRD scheme
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, scopes, usedVals)
        // val fImplications = Symmetry.drdFunctionImplicationsSimplified(f, scopes, usedVals)
        addRangeRestrictions(fRangeRestrictions)
        // addGeneralConstraints(fImplications)
    }
}

object Imp0SymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new Imp0SymmetryBreaker(theory, scopes)
}

// No implications for functions or constants (but still for predicates)
class Imp1SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DefaultPredicateBreaking
with DrdDifferentiation
with DefaultNonDrdScheme {
    
    override def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for(sort <- theory.sorts if !sort.isBuiltin && tracker.stillUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val usedVals = tracker.usedDomainElements(sort).toIndexedSeq
            val scope = scopes(sort)
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, scope, usedVals)
            val constantImplications = Symmetry.csConstantImplications(sort, constants, scope, usedVals)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // DRD scheme
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, scopes, usedVals)
        val fImplications = Symmetry.drdFunctionImplications(f, scopes, usedVals)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
    }
}

object Imp1SymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new Imp1SymmetryBreaker(theory, scopes)
}
