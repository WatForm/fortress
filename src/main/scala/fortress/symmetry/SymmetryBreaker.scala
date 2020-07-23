package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

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
        if(P.argSorts forall (tracker.view.numUnusedDomainElements(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
            val pImplications = Symmetry.predicateImplications(P, tracker.view)
            addGeneralConstraints(pImplications)
        }
    }
}

trait DrdDifferentiation extends SymmetryBreaker {
    def breakDrdFunction(f: FuncDecl): Unit
    def breakNonDrdFunction(f: FuncDecl): Unit
    
    override def breakFunction(f: FuncDecl): Unit = {
        if(tracker.view.existsUnusedDomainElements(f.resultSort)) {
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
        for(sort <- theory.sorts if !sort.isBuiltin && tracker.view.existsUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, tracker.view)
            val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, tracker.view)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, tracker.view)
        val fImplications = Symmetry.drdFunctionImplicationsSimplified(f, tracker.view)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
    }
}

object DefaultSymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new DefaultSymmetryBreaker(theory, scopes)
}
