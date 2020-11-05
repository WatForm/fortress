package fortress.transformers

import scala.language.implicitConversions
import fortress.msfol.Theory

/** An abstraction of a function from Theory to Theory. */
trait TheoryTransformer {
    
    /** Takes in a theory, applies some transformation to it, and produces a
    * new theory. Note that this does not mutate the theory object, only
    * produces a new one. */
    def apply(theory: Theory): Theory
    
    def name: String
}

object TheoryTransformer {
    implicit def asProblemStateTransformer(theoryTransformer: TheoryTransformer): ProblemStateTransformer = {
        object asPST extends ProblemStateTransformer {
            override def apply(problemState: ProblemState): ProblemState = {
                ProblemState(
                    theoryTransformer(problemState.theory),
                    problemState.scopes,
                    problemState.skolemConstants,
                    problemState.skolemFunctions,
                    problemState.rangeRestrictions,
                    problemState.unapplyInterp
                )
            }
            
            override def name = theoryTransformer.name
        }
        asPST
    }
}
