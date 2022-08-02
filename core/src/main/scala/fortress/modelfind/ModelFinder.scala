package fortress.modelfind

import fortress.msfol._

import fortress.interpretation._
import fortress.solverinterface._
import fortress.logging._

import java.lang.AutoCloseable
import fortress.util._

/** The various return possibilities of the model finder.
  * SAT means the theory is satisfiable.
  * UNSAT means the theory is unsatisfiable.
  * TIMEOUT means the model finder could not be determined within the time limit.
  * UNKNOWN means the satisfiability of the theory could not be determined for another reason,
  * such as the underlying solver giving up, which is valid behaviour in undecidable logics.
  * ERROR means there was a fatal problem; this is not expected behaviour and indicates a bug.
  */
sealed trait ModelFinderResult

case object SatResult extends ModelFinderResult {
    override def toString = "Sat"
}
case object UnsatResult extends ModelFinderResult {
    override def toString = "Unsat"
}
case object UnknownResult extends ModelFinderResult {
    override def toString = "Unknown"
}
case object TimeoutResult extends ModelFinderResult {
    override def toString = "Timeout"
}
case class ErrorResult(message: String) extends ModelFinderResult {
    override def toString = s"Error (${message})"
}

object ModelFinderResult {
    val Sat: ModelFinderResult = SatResult
    val Unsat: ModelFinderResult = UnsatResult
    val Unknown: ModelFinderResult = UnknownResult
    val Timeout: ModelFinderResult = TimeoutResult
}

/**
  * Top-level interface to search for satisfying models to theories with scopes.
  * Extends AutoCloseable because it may hold a resource, such as an open connection to an SMT solver, which must be closed.
  */
trait ModelFinder extends AutoCloseable {

    /** Set the theory of the model finder. */
    def setTheory(theory: Theory): Unit

    /** Set the scope of the given sort, which is the size of the domain for that sort. */
    def setAnalysisScope(t: Sort, size: Int, isExact: Boolean): Unit

    /** Set the timeout in milliseconds. */
    def setTimeout(milliseconds: Milliseconds): Unit

    /** Set the timeout in seconds. */
    def setTimeout(seconds: Seconds): Unit = {
        setTimeout(seconds.toMilli)
    }

    // Parentheses are used rather than zero parameters to indicate that state may change.

    /** Check for a satisfying interpretation to the theory with the given scopes. */
    def checkSat(): ModelFinderResult 

    /** View the satisfying interpretation, if one exists.
      * Otherwise, throws an error.
      * Can only be called after checkSat.
      */
    def viewModel(): Interpretation

    /** Return the next satisfying interpretation. */
    def nextInterpretation(): ModelFinderResult

    /** Count the total number of satisfying interpretations. */
    def countValidModels(newTheory: Theory): Int
    
    // Internal use only

    def setOutput(log: java.io.Writer): Unit
    def addLogger(logger: EventLogger): Unit
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit
}

object ModelFinder {
    def createDefault(): ModelFinder = new FortressFOUR_SI

    def createPredUpperBoundModelFinder(): ModelFinder = new PredUpperBoundModelFinder
}

