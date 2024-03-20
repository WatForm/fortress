package fortress.transformers

import scala.language.implicitConversions
import fortress.msfol.Theory
import fortress.problemstate.ProblemState
import fortress.problemstate.Flags

/** A transformation from Theory to Theory. */
trait TheoryTransformer extends Function[Theory, Theory] {
    
    def apply(theory: Theory, flags: Flags): Theory
    
    def name: String
}

object TheoryTransformer {
    
    /** Implicit conversion from TheoryTransformer to ProblemStateTransformer */
    implicit def asProblemStateTransformer(theoryTransformer: TheoryTransformer): ProblemStateTransformer = {
        object asPST extends ProblemStateTransformer {
            override def apply(problemState: ProblemState): ProblemState = {
                problemState.copy(
                    theory = theoryTransformer(problemState.theory, problemState.flags)
                )
            }
            
            override def name = theoryTransformer.name
        }
        asPST
    }
}
