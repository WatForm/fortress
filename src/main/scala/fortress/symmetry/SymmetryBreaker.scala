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
    
    protected val tracker = DomainElementTracker.create(theory, scopes)
    
    // Accumulates the symmetry breaking constraints
    protected val newConstraints = new mutable.ListBuffer[Term]
    protected val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
    protected val newDeclarations = new mutable.ListBuffer[FuncDecl]
    
    final def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for(sort <- theory.sorts if !sort.isBuiltin && view.existsFreshValue(sort)) {
            breakConstants(sort, constantsToBreak.filter(_.sort == sort).toIndexedSeq)
        }
    }
    
    protected def breakConstants(sort: Sort, constants: IndexedSeq[AnnotatedVar]): Unit
    
    def breakFunction(f: FuncDecl): Unit
    def breakPredicate(P: FuncDecl): Unit
    
    def constraints: Seq[Term] = newConstraints.toList
    def rangeRestrictions: Seq[RangeRestriction] = newRangeRestrictions.toList
    def declarations: Seq[FuncDecl] = newDeclarations.toList
    
    def view: DomainElementUsageView = tracker.view
    
    protected def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
        // Add to constraints
        newConstraints ++= rangeRestrictions map (_.asFormula)
        newRangeRestrictions ++= rangeRestrictions
        // Add to used values
        tracker.markStale(rangeRestrictions flatMap (_.asFormula.domainElements))
    }
    
    protected def addGeneralConstraints(fmls: Set[Term]): Unit = {
        // Add to constraints
        newConstraints ++= fmls
        // Add to used values
        tracker.markStale(fmls flatMap (_.domainElements))
    }
    
    protected def addDeclaration(f: FuncDecl): Unit = {
        newDeclarations += f
    }
}

trait DefaultPredicateBreaking extends SymmetryBreaker {
    override def breakPredicate(P: FuncDecl): Unit = {
        if(P.argSorts forall (view.numFreshValues(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
            val pImplications = Symmetry.predicateImplications(P, view)
            addGeneralConstraints(pImplications)
        }
    }
}

trait DependenceDifferentiation extends SymmetryBreaker {
    def breakRDDFunction(f: FuncDecl): Unit
    def breakRDIFunction(f: FuncDecl): Unit
    
    override def breakFunction(f: FuncDecl): Unit = {
        if(view.existsFreshValue(f.resultSort)) {
            if (f.isRDD) {
                breakRDDFunction(f)
            } else {
                breakRDIFunction(f)
            }
        }
    }
}

trait DefaultRDDScheme extends DependenceDifferentiation {
    override def breakRDDFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = Symmetry.rddFunctionRangeRestrictions_UsedFirst(f, view)
        addRangeRestrictions(fRangeRestrictions)
    }
}

trait DefaultRDIScheme extends DependenceDifferentiation {
    override def breakRDIFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = Symmetry.rdiFunctionRangeRestrictions(f, view)
        val fImplications = Symmetry.rdiFunctionImplicationsSimplified(f, view)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
    }
}

trait DefaultConstantScheme extends SymmetryBreaker {
    override def breakConstants(sort: Sort, constants: IndexedSeq[AnnotatedVar]): Unit = {
        val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, view)
        val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, view)
        
        addRangeRestrictions(constantRangeRestrictions)
        addGeneralConstraints(constantImplications)
    }
}

// Concrete Implementations

class DefaultSymmetryBreaker(theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DefaultPredicateBreaking
with DependenceDifferentiation
with DefaultConstantScheme
with DefaultRDIScheme
with DefaultRDDScheme

object DefaultSymmetryBreaker extends SymmetryBreakerFactory {
    def create(theory: Theory, scopes: Map[Sort, Int]): SymmetryBreaker = new DefaultSymmetryBreaker(theory, scopes)
}
