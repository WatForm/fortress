package fortress.msfol

object Names {
    private val illegalNames: Set[String] = Set(
        "and", "or", "not", "=>", "<=>", "iff",
        "forall", "exists", "=", "==",
        "true", "false", 
        "if", "else"
    )
    
    private val illegalPrefixes: Set[String] = Set(
        DomainElement.prefix
    )
    
    def isIllegal(name: String): Boolean =
        (illegalNames contains name.toLowerCase) || (illegalPrefixes exists (name startsWith _))
}
