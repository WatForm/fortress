package fortress.modelfind

import fortress.msfol._

import fortress.interpretation._
import fortress.solverinterface._

/** The various return possibilities of the model finder.
* SAT means the theory is satisfiable.
* UNSAT means the theory is unsatisfiable.
* TIMEOUT means the model finder could not be determined within the time limit.
* UNKNOWN means the satisfiability of the theory could not be determined for another reason,
* such as the underlying solver giving up, which is valid behaviour in undecidable logics.
* ERROR means there was a fatal problem; this is not expected behaviour. */
sealed trait ModelFinderResult

case object SatResult extends ModelFinderResult
case object UnsatResult extends ModelFinderResult
case object UnknownResult extends ModelFinderResult
case object TimeoutResult extends ModelFinderResult
case object ErrorResult extends ModelFinderResult

object ModelFinderResult {
    val Sat: ModelFinderResult = SatResult
    val Unsat: ModelFinderResult = UnsatResult
    val Unknown: ModelFinderResult = UnknownResult
    val Timeout: ModelFinderResult = TimeoutResult
    val Error: ModelFinderResult = ErrorResult
}

/** Invoked to search for satisfying models to theories. */
trait ModelFinder {
    def setTheory(theory: Theory): Unit
    def setAnalysisScope(t: Sort, size: Int): Unit
    def setTimeout(milliseconds: Int): Unit
    // Parantheses are used rather than zero parameters to indicate that state may change.
    def checkSat(): ModelFinderResult
    def viewModel(): Interpretation
    
    // Internal use only
    def setOutput(log: java.io.Writer): Unit
    def setDebug(enableDebug: Boolean): Unit
}

object ModelFinder {
    def createDefault(): ModelFinder = new EufSmtModelFinder(new Z3ApiSolver())
}