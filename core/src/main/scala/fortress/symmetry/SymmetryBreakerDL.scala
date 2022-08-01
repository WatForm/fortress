package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

trait SymmetryBreakerFactoryDL {
    def create(theory: Theory, scopes: Map[Sort, Scope], stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker): SymmetryBreakerDL
}

abstract class SymmetryBreakerDL(
                                  theory: Theory,
                                  protected val scopes: Map[Sort, Scope],
                                  stalenessTrackerParam: StalenessTracker,
                                  remainingTrackerParam: RemainingIdentifiersTracker,
                                  disjunctsLimitParam: Option[Int] = None
                                ) {

    protected val stalenessTracker: StalenessTracker = stalenessTrackerParam
    protected val remainingTracker: RemainingIdentifiersTracker = remainingTrackerParam
    protected val disjunctsLimit: Option[Int] = disjunctsLimitParam

    // Accumulates the symmetry breaking constraints
    protected val newConstraints = new mutable.ListBuffer[Term]
    protected val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
    protected val newDeclarations = new mutable.ListBuffer[FuncDecl]

    // Perform symmetry breaking on constants, one sort by another
    final def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
        for (sort <- theory.sorts if !sort.isBuiltin && stalenessTracker.state.existsFreshValue(sort)) {
            breakConstants(sort, constantsToBreak.filter(_.sort == sort).toIndexedSeq)
        }
    }

    // Perform symmetry breaking on constants, one sort by another(preserve the order)
    def breakListOfConstants(constantsToBreak: IndexedSeq[AnnotatedVar]): Unit = {
        val constantsGroupedBySort = constantsToBreak.groupBy(_.sort)
        for ((sort, constants) <- constantsGroupedBySort if !sort.isBuiltin && stalenessTracker.state.existsFreshValue(sort)) {
            breakConstants(sort, constants)
        }
    }

    // Perform symmetry breaking on constants of the input sort.
    protected def breakConstants(sort: Sort, constants: IndexedSeq[AnnotatedVar]): Unit

    def breakFunction(f: FuncDecl): Unit

    def breakPredicate(P: FuncDecl): Unit

    def constraints: Seq[Term] = newConstraints.toList

    def rangeRestrictions: Seq[RangeRestriction] = newRangeRestrictions.toList

    def declarations: Seq[FuncDecl] = newDeclarations.toList

    def stalenessState: StalenessState = stalenessTracker.state

    protected def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
        // Add to constraints
        newConstraints ++= rangeRestrictions map (_.asFormula)
        newRangeRestrictions ++= rangeRestrictions
        // Add to used values
        stalenessTracker.markStale(rangeRestrictions flatMap (_.asFormula.domainElements))
    }

    protected def addGeneralConstraints(fmls: Set[Term]): Unit = {
        // Add to constraints
        newConstraints ++= fmls
        // Add to used values
        stalenessTracker.markStale(fmls flatMap (_.domainElements))
    }

    protected def addDeclaration(f: FuncDecl): Unit = {
        newDeclarations += f
    }
}

trait DefaultPredicateBreakingDL extends SymmetryBreakerDL {
    override def breakPredicate(P: FuncDecl): Unit = {
        if (P.argSorts forall (stalenessTracker.state.numFreshValues(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
            val pImplications = SymmetryDL.predicateImplications(P, stalenessTracker.state, disjunctsLimit)
            addGeneralConstraints(pImplications)
            if (pImplications.nonEmpty) remainingTracker.markUsedFuncDecls(P)
        }
    }
}

trait DependenceDifferentiationDL extends SymmetryBreakerDL {
    def breakRDDFunction(f: FuncDecl): Unit

    def breakRDIFunction(f: FuncDecl): Unit

    override def breakFunction(f: FuncDecl): Unit = {
        def flag: Boolean = {
            var temp = true
            for ( item <- f.argSorts ) {
                if (!scopes.contains(item)) {
                    temp = false
                }
            }
            if( !scopes.contains(f.resultSort) ) {
                temp = false
            }
            temp
        }
        if( flag) {
            if (stalenessTracker.state.existsFreshValue(f.resultSort)) {
                if (f.isRDD) {
                    breakRDDFunction(f)
                } else {
                    breakRDIFunction(f)
                }
            }
        }
    }
}

trait DefaultRDDSchemeDL extends DependenceDifferentiationDL {
    override def breakRDDFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = SymmetryDL.rddFunctionRangeRestrictions_UsedFirst(f, stalenessTracker.state, disjunctsLimit)
        addRangeRestrictions(fRangeRestrictions)
        if (fRangeRestrictions.nonEmpty) remainingTracker.markUsedFuncDecls(f)
    }
}


trait DefaultRDISchemeDL extends DependenceDifferentiationDL {
    override def breakRDIFunction(f: FuncDecl): Unit = {
        val fRangeRestrictions = SymmetryDL.rdiFunctionRangeRestrictions(f, stalenessTracker.state, disjunctsLimit)
        val fImplications = SymmetryDL.rdiFunctionImplicationsSimplified(f, stalenessTracker.state, fRangeRestrictions.size)
        addRangeRestrictions(fRangeRestrictions)
        addGeneralConstraints(fImplications)
        if (fRangeRestrictions.nonEmpty) remainingTracker.markUsedFuncDecls(f)
    }
}


trait DefaultConstantSchemeDL extends SymmetryBreakerDL {
    override def breakConstants(sort: Sort, constants: IndexedSeq[AnnotatedVar]): Unit = {
        val constantRangeRestrictions = SymmetryDL.csConstantRangeRestrictions(sort, constants, stalenessTracker.state, disjunctsLimit)
        val constantImplications = SymmetryDL.csConstantImplicationsSimplified(sort, constants, stalenessTracker.state, constantRangeRestrictions.size)

        addRangeRestrictions(constantRangeRestrictions)
        addGeneralConstraints(constantImplications)
        remainingTracker.markUsedConstants(constants.take(constantRangeRestrictions.size): _*)
    }
}

// Concrete Implementations

class DefaultSymmetryBreakerDL(theory: Theory, scopes: Map[Sort, Scope], stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker, disjunctsLimitParam: Option[Int])
  extends SymmetryBreakerDL(theory, scopes, stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker, disjunctsLimitParam: Option[Int])
    with DefaultPredicateBreakingDL
    with DependenceDifferentiationDL
    with DefaultConstantSchemeDL
    with DefaultRDISchemeDL
    with DefaultRDDSchemeDL

case class DefaultSymmetryBreakerFactoryDL(disjunctsLimit: Option[Int] = None) extends SymmetryBreakerFactoryDL {
    def create(theory: Theory, scopes: Map[Sort, Scope], stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker): SymmetryBreakerDL = new DefaultSymmetryBreakerDL(theory, scopes, stalenessTracker, remainingTracker, disjunctsLimit)
}

