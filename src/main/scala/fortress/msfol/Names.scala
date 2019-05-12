package fortress.msfol

object Names {
    private val illegalNames: Set[String] = Set(
        "and", "or", "not", "=>", "<=>", "iff",
        "forall", "exists", "=", "==",
        "true", "false", 
        "if", "else"
    )
    
    def isIllegal(name: String): Boolean =  (illegalNames contains name.toLowerCase)
}
