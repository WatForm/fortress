package fortress.transformers

import fortress.msfol.Theory

/** An abstraction of a function from Theory to Theory. */
trait TheoryTransformer {
    
    /** Takes in a theory, applies some transformation to it, and produces a
    * new theory. Note that this does not mutate the theory object, only
    * produces a new one. */
    def apply(theory: Theory): Theory
    
    def name: String
}
