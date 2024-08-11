package fortress.modelfinders

import fortress.problemstate.{TrivialResult, TrivialSat, TrivialUnsat}

import scala.language.implicitConversions

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

    implicit def fromTrivialResult(trivialResult: TrivialResult): ModelFinderResult = trivialResult match {
        case TrivialSat => Sat
        case TrivialUnsat => Unsat
    }
}