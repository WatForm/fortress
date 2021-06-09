package fortress.msfol

/** Stores and tests for illegal names. */ 
object Names {
    private val illegalNames: Set[String] = Set(
        "and", "or", "not", "=>", "<=>", "iff",
        "forall", "exists", "=", "==",
        "true", "false", 
        "if", "else"
    )
    
    private val illegalPrefixes: Set[String] = Set(
        DomainElement.prefix,
        "@",
        "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"
    )
    
    def isIllegal(name: String): Boolean =
        (illegalNames contains name.toLowerCase) || (illegalPrefixes exists (name startsWith _))
}
