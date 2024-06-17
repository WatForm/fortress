package fortress.problemstate

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.util.Errors

/**
  * Contains flags for a problem state
  *
  * @param distinctConstants
  * @param haveRunNNF Is the problem state in negation normal form
  * @param verbose Debug verbose output should be printed
  */
case class Flags private(
    distinctConstants: Boolean = true,

    haveRunNNF: Boolean = false,
    haveRunIfLifting: Boolean = false,
    haveRunSkolemizer: Boolean = false,

    haveRunMaxAlphaRenaming: Boolean = false,
    
    verbose: Boolean = false,
    
    // typechecker turns these on if these exist in the axioms/defns
    // but transformers (IfLifting, Skolemize) cannot turn them off
    // because all Ites or quantifiers may not have been eliminated
    
    // the typechecker or problemstate constructor sets these flags
    // however transformers can introduce these after typechecking, creation
    // so we should perhaps drop these flags
    // we can't use them to decide whether to run certain transformers or no
    containsItes: Boolean = false,  
    containsExists: Boolean = false,
    containsNonExactScopes: Boolean = false,
) {}

case object Flags {
    def default: Flags = Flags()
}