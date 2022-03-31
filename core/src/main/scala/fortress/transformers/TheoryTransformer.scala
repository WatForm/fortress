package fortress.transformers

import scala.language.implicitConversions
import fortress.msfol.Theory

/** A transformation from Theory to Theory. */
trait TheoryTransformer extends Function[Theory, Theory] {
    
    def apply(theory: Theory): Theory
    
    def name: String
}

object TheoryTransformer {
    
    /** Implicit conversion from TheoryTransformer to ProblemStateTransformer */
    implicit def asProblemStateTransformer(theoryTransformer: TheoryTransformer): ProblemStateTransformer = {
        object asPST extends ProblemStateTransformer {
            override def apply(problemState: ProblemState): ProblemState = {
                ProblemState(
                    theoryTransformer(problemState.theory),
                    problemState.scopes,
                    problemState.skolemConstants,
                    problemState.skolemFunctions,
                    problemState.rangeRestrictions,
                    problemState.unapplyInterp,
                    problemState.distinctConstants
                )
            }
            
            override def name = theoryTransformer.name
        }
        asPST
    }
}
