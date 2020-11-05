package fortress.transformers

import fortress.msfol._

/** An abstraction of a function from ProblemState to ProblemState. */
trait ProblemStateTransformer extends {
    
    /** Takes in a Problem, applies some transformation to it, and produces a
    * new ProblemState. Note that this does not mutate the ProblemState object, only
    * produces a new one. */
    def apply(problemState: ProblemState): ProblemState
    
    def name: String
}

// Separate trait to emphasize that this is not the main use of ProblemStateTransformer
// This is mostly here to facilitate simpler unit tests
trait TheoryApplication extends ProblemStateTransformer {
    def apply(theory: Theory): Theory = apply(ProblemState(theory)).theory
}