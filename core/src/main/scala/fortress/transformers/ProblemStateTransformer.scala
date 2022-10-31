package fortress.transformers

import fortress.msfol._
import fortress.problemstate.ProblemState

/** A transformation from ProblemState to ProblemState. */
trait ProblemStateTransformer extends Function[ProblemState, ProblemState] {
    
    /** Takes in a Problem, applies some transformation to it, and produces a
    * new ProblemState. Note that this does not mutate the ProblemState object, only
    * produces a new one. */
    def apply(problemState: ProblemState): ProblemState
    
    def name: String
}
