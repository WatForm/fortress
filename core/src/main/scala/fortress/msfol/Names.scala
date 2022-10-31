package fortress.msfol

/** Stores and tests for illegal names. */
object Names {
    private val illegalNames: Set[String] = Set.empty
    /**
      * SMT-LIB reserved keywords: "and", "or", "not", "=>", "<=>", "iff",
      * "forall", "exists", "=", "==", "true", "false", "if", "else"
      * The reason we can't use those names is that when we output the SMT-LIB
      * string, the SMT solver would be confused if we have a variable named
      * e.g. "not" that wasn't meant to be the logical not operation.
      *
      * But now we are adding suffix to all variable, function names when
      * converting to SMT-LIB, so this is no longer a problem.
      */


    private val illegalPrefixes: Set[String] = Set(
        DomainElement.prefix,
//        "@",
        "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"
    )

    def isIllegal(name: String): Boolean = illegalPrefixes exists (name startsWith _)
}
