package fortress.problemstate

/**
  * Contains flags for a problem state
  *
  * @param distinctConstants
  * @param haveRunNNF Is the problem state in negation normal form
  * @param verbose Debug verbose output should be printed
  */
case class Flags (
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
    constains2ndOrderQuantifiers: Boolean = false,

    // This should be set if a transformer determines that the model is trivial.
    trivialResult: Option[TrivialResult] = None,
) {}

// Flags.default is the same as doing Flags() or new Flags()
case object Flags {
    def default: Flags = Flags()
}