package fortress.transformers

import fortress.operations.EvaluationInliner
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/**
  * A transformer that evaluates terms that are independent of the interpretation.
  */
object EvaluateTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        val inliner = new EvaluationInliner(problemState.theory)
        problemState.copy(theory = problemState.theory.mapAllTerms(inliner.naturalRecur))
    }

}
