package fortress.transformers

import fortress.msfol.Problem

/** An abstraction of a function from Problem to Problem. */
trait ProblemTransformer {
    
    /** Takes in a Problem, applies some transformation to it, and produces a
    * new Problem. Note that this does not mutate the Problem object, only
    * produces a new one. */
    def apply(problem: Problem): Problem
    
    def name: String
}
