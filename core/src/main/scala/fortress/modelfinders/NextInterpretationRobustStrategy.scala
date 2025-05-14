package fortress.modelfinders

import fortress.util._
import fortress.util.Control.measureTime
import fortress.msfol._
import fortress.interpretation._
import fortress.compilers._
import fortress.solvers._
import fortress.logging._
import fortress.problemstate._

import scala.collection.mutable

trait NextInterpretationRobustStrategy extends ModelFinder {

    protected var theory: Theory
    protected var solver: Solver
    protected var timeoutMilliseconds: Milliseconds

    protected var haveSolved: Boolean
    // only contains a valid value if haveCompiled is true
    protected var compilerResult: Either[CompilerError, CompilerResult]
    // only useful to viewModels if it has a SatSolution
    protected var hasSatSolution: Boolean
    // if the model is trivially SAT, here's its interpretation
    protected var trivialSolution: Option[Interpretation]

    /* Track the constraints for next interpretation */
    private val nextInterpConstraints: mutable.ListBuffer[Term] = new mutable.ListBuffer

    protected def clearNextInterpretation(): Unit = {
        nextInterpConstraints.clear()
    }

    /** Return the next satisfying interpretation. */
    def nextInterpretation(): ModelFinderResult = {

        // have to have solved first, although if this is called directly, then
        // user would never see first interpretation
        if (!haveSolved) checkSat(alwaysSolve = true)
        if (!hasSatSolution) Errors.Internal.impossibleState("can only view models if the problem is SAT")
        // We can only get the next interpretation if we have gone to the solver
        // This is why we pass alwaysSolve above
        if (trivialSolution.isDefined) Errors.Internal.preconditionFailed("Can only get the next interpretation if not trivial")

        // Negate the current interpretation, but leave out the skolem functions
        // Different witnesses are not useful for counting interpretations
        // todo: given the unapply methods, do we still need skipForNextInterpretation?

        val instance = viewModel()
            .withoutDeclarations(compilerResult.right.get.skipForNextInterpretation)

        /* Note: if in the future we use incremental solving instead of closing the solver and spinning up a new solver,
        * the quantifiers present in newAxiom will need to be explicitly expanded. This is not just a performance issue,
        * but a correctness issue - we cannot leave quantifiers in place for uninterpreted types that we use range formulas to restrict their
        * scopes.
        */

        // println("Instance")
        // println(instance)
        val newAxiom = Not(And.smart(instance.toConstraints.toList))
        nextInterpConstraints += newAxiom

        val nextInterpTheory = theory.withAxioms(nextInterpConstraints.toList)

        // println("Next Theory")
        // println(nextInterpTheory)
        setTheory(nextInterpTheory)
        checkSat(verbose = false, alwaysSolve = true)
    }
}
