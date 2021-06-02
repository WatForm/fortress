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
* ERROR means there was a fatal problem; this is not expected behaviour. */
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
  */
trait ModelFinder extends AutoCloseable {
    def setTheory(theory: Theory): Unit
    def setAnalysisScope(t: Sort, size: Int): Unit
    def setTimeout(milliseconds: Milliseconds): Unit
    def setTimeout(seconds: Seconds): Unit = {
        setTimeout(seconds.toMilli)
    }
    def setBoundedIntegers(semantics: IntegerSemantics): Unit
    // Parentheses are used rather than zero parameters to indicate that state may change.
    def checkSat(): ModelFinderResult
    def viewModel(): Interpretation

    // Used for counting valid models
    def nextInterpretation(): ModelFinderResult
    def countValidModels(newTheory: Theory): Int
    
    // Internal use only
    def setOutput(log: java.io.Writer): Unit
    def addLogger(logger: EventLogger): Unit
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit
}

object ModelFinder {
    def createDefault(): ModelFinder = new FortressZERO
}

sealed trait IntegerSemantics
case object Unbounded extends IntegerSemantics
case class ModularSigned(bitwidth: Int) extends IntegerSemantics

object IntegerSemantics {
    val UnboundedSemantics: IntegerSemantics = Unbounded
    def ModularSignedSemantics(bitwidth: Int): IntegerSemantics = ModularSigned(bitwidth)
}
