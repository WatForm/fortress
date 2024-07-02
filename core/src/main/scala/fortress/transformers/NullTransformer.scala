package fortress.transformers

import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.util.Errors

object NullTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        problemState
    }

    override def name: String = "NullTransformer"

}