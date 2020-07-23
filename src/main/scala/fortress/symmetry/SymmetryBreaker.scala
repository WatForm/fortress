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
    val newDeclarations = new mutable.ListBuffer[FuncDecl]
    
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
    
    protected def addDeclaration(f: FuncDecl): Unit = {
        newDeclarations += f
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
        val fRangeRestrictions = Symmetry.csFunctionExtRangeRestrictions(f, tracker.view)
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
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, tracker.view)
            val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, tracker.view)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // DRD scheme
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, tracker.view)
        val fImplications = Symmetry.drdFunctionImplicationsSimplified(f, tracker.view)
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
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, tracker.view)
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
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, tracker.view)
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
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, tracker.view)
            val constantImplications = Symmetry.csConstantImplications(sort, constants, tracker.view)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val resultSort = f.resultSort
        val scope = scopes(resultSort)
        val usedVals = tracker.usedDomainElements(resultSort).toIndexedSeq
        
        // DRD scheme
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, tracker.view)
        val fImplications = Symmetry.drdFunctionImplications(f, tracker.view)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
    }
}

object Imp1SymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new Imp1SymmetryBreaker(theory, scopes)
}

// Just Neq
class Neq0SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int]) extends DefaultSymmetryBreaker(theory, scopes) {
    override protected def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
        // Add to constraints
        constraints ++= rangeRestrictions flatMap (rr => {
            val sort = rr.sort
            val allDomainElems = (1 to scopes(sort)) map (i => DomainElement(i, sort))
            rr.asNeqs(allDomainElems)
        })
        newRangeRestrictions ++= rangeRestrictions
        // Add to used values
        tracker.markUsed(rangeRestrictions flatMap (_.asFormula.domainElements))
    }
}

object Neq0SymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new Neq0SymmetryBreaker(theory, scopes)
}

// Neq and OrEqs
class Neq1SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int]) extends DefaultSymmetryBreaker(theory, scopes) {
    override protected def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
        // Add to constraints
        constraints ++= rangeRestrictions flatMap (rr => {
            val sort = rr.sort
            val allDomainElems = (1 to scopes(sort)) map (i => DomainElement(i, sort))
            rr.asNeqs(allDomainElems) :+ rr.asFormula
        })
        newRangeRestrictions ++= rangeRestrictions
        // Add to used values
        tracker.markUsed(rangeRestrictions flatMap (_.asFormula.domainElements))
    }
}

object Neq1SymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new Neq1SymmetryBreaker(theory, scopes)
}

class RainbowSymmetryBreaker (theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DrdDifferentiation {
    override def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = { }
    override def breakNonDrdFunction(f: FuncDecl): Unit = { }
    override def breakPredicate(P: FuncDecl): Unit = { }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        if (
            f.arity <= 2
            && f.isRainbowSorted
            && (f.resultSort +: f.argSorts).forall(tracker.usedDomainElements(_).isEmpty)
        ) {
            val usedValues: Map[Sort, IndexedSeq[DomainElement]] = tracker.usedDomainElements map {
                case (sort, setOfVals) => (sort, setOfVals.toIndexedSeq)
            }
            val (ltDecl, formulas, rangeRestrictions) = Symmetry.rainbowFunctionLT(f, scopes, usedValues)
            addDeclaration(ltDecl)
            addRangeRestrictions(rangeRestrictions.toSet)
            addGeneralConstraints(formulas.toSet)
        }
    }
}
