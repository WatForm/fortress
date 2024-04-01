package fortress.problemstate

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.util.Errors

/**
  * Contains flags for a problem state
  *
  * @param distinctConstants
  * @param isNNF Is the problem state in negation normal form
  * @param verbose Debug verbose output should be printed
  */
case class Flags private(
    distinctConstants: Boolean = true,
    isNNF: Boolean = false,
    verbose: Boolean = false,
    containsIte: Boolean = false,
) {}

case object Flags {
    def default: Flags = Flags()
}