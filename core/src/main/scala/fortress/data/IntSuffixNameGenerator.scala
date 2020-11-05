package fortress.data

/** Generates names using integer suffixes. For example, for starting index 1 atEnd
 * given the string "base", this generator will try the names "base_1",
 * "base_2", "base_3", ... until it it finds a name that is not forbidden. */
class IntSuffixNameGenerator(
    private var forbiddenNames: Set[String],
    private var startingIndex: Int)
    extends NameGenerator {
    
    // TODO: could be implemented more efficiently in cases where we know
    // we are likely to use the same base often.
    
    override def freshName(base: String): String = {
        var i = startingIndex
        var candidate = base + "_" + i
        while(forbiddenNames contains candidate) {
            i += 1
            candidate = base + "_" + i
        }
        forbidName(candidate)
        candidate
    }
    
    override def forbidName(name: String): Unit = {
        forbiddenNames = forbiddenNames + name
    }
}
