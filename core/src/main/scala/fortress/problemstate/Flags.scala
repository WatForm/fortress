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

    haveRunNNF: Boolean = false,
    haveRunIfLifting: Boolean = false,
    haveRunSkolemizer: Boolean = false,
    
    verbose: Boolean = false,
    
    // typechecker turns these on if these exist in the axioms/defns
    // but transformers (IfLifting, Skolemize) cannot turn them off
    // because all Ites or quantifiers may not have been eliminated
    
    containsItes: Boolean = false,  
    containsExists: Boolean = false,

    containsNonExactScopes: Boolean = false,
) {}

case object Flags {
    def default: Flags = Flags()
}