package fortress.problemstate

sealed trait TrivialResult

// Represents that the problem is trivially valid.
case object TrivialValid extends TrivialResult

// Represents that the problem is trivially unsatisfiable.
case object TrivialUnsat extends TrivialResult

object TrivialResult {
    val Valid: TrivialResult = TrivialValid
    val Unsat: TrivialResult = TrivialUnsat
}