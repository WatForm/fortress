package fortress.transformers

/** An abstraction of a function from ProblemState to ProblemState. */
trait ProblemStateTransformer extends {
    
    /** Takes in a Problem, applies some transformation to it, and produces a
    * new ProblemState. Note that this does not mutate the ProblemState object, only
    * produces a new one. */
    def apply(problemState: ProblemState): ProblemState
    
    def name: String
}
