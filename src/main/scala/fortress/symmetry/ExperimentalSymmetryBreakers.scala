package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

// No implications for functions or constants (but still for predicates)
class Imp0SymmetryBreaker(theory: Theory, scopes: Map[Sort, Int])
extends SymmetryBreaker(theory, scopes)
with DefaultPredicateBreaking
with DrdDifferentiation
with DefaultNonDrdScheme {
    
    override def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for(sort <- theory.sorts if !sort.isBuiltin && view.existsUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, view)
            // val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, scope, usedVals)
            
            addRangeRestrictions(constantRangeRestrictions)
            // addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, view)
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
        for(sort <- theory.sorts if !sort.isBuiltin && view.existsUnusedDomainElements(sort)) {
            val constants = constantsToBreak.filter(_.sort == sort).toIndexedSeq
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, view)
            val constantImplications = Symmetry.csConstantImplications(sort, constants, view)
            
            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }
    }
    
    override def breakDrdFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = Symmetry.drdFunctionRangeRestrictions(f, view)
        val fImplications = Symmetry.drdFunctionImplications(f, view)
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
        newConstraints ++= rangeRestrictions flatMap (rr => {
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
        newConstraints ++= rangeRestrictions flatMap (rr => {
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
            && (f.resultSort +: f.argSorts).forall(view.usedDomainElements(_).isEmpty)
        ) {
            val (ltDecl, formulas, rangeRestrictions) = Symmetry.rainbowFunctionLT(f, view)
            addDeclaration(ltDecl)
            addRangeRestrictions(rangeRestrictions.toSet)
            addGeneralConstraints(formulas.toSet)
        }
    }
}
