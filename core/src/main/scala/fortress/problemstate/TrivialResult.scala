package fortress.problemstate

sealed trait TrivialResult

case object TrivialSat extends TrivialResult
case object TrivialUnsat extends TrivialResult

object TrivialResult {
    val Sat: TrivialResult = TrivialSat
    val Unsat: TrivialResult = TrivialUnsat
}