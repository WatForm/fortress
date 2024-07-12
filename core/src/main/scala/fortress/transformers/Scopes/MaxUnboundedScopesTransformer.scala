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

        print("Scopes before MaxUnbounded Scopes Transformer")
        println(scopes)

        for (sc <- scopes)
            println(sc._2.isFixed())

        // by removing fixed sorts of fixed scope
        // from the scope set, they become unbounded
        val new_scopes = scopes.filter( _._2.isFixed() )

        print("Scopes after MaxUnbounded Scopes Transformer")
        println(new_scopes)

        problemState.copy(scopes = new_scopes)

    }


}
