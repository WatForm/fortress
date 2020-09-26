package fortress.data

/** Generates fresh names. Has mutable state. */
trait NameGenerator {
    
    /** Genereate a fresh name and forbids it from use in the future.
     * Uses the given base string to generate the new name, though it may
     * not match exactly (e.g. when asking for "a", it may give "a_2" if there
     * are conflicts with forbidden names).
     * This method will mutate the name generator. */
    def freshName(base: String): String
    
    /** Forbids a name from future name generation. */
    def forbidName(name: String): Unit
}
