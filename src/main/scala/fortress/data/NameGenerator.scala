package fortress.data

trait NameGenerator {
    
    // This method is expected to mutate the name generator
    // and forbid the resulting name from being used in the future
    def freshName(base: String): String
    
    // This method is expected to mutate the name generator
    // and prevent the given name from being used in the future
    def forbidName(name: String): Unit
}
