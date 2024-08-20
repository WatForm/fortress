package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState


object MaxUnboundedScopesTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes

        // keep only the fixed sorts
        // the sorts no longer in the scopes map become unbounded
        val newScopes = scopes.filter({case (_, scope) => scope.isFixed()})  
        
        problemState.withScopes(newScopes)
    }


}
