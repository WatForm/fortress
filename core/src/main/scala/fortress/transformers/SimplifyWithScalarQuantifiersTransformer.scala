package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

object SimplifyWithScalarQuantifiersTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        val newTheory = problemState.theory
        .mapAllTerms(_.simplify)  // necessary before ScalarQuantifierSimplifier
        .mapAllTerms(ScalarQuantifierSimplifier.simplify)
        .mapAllTerms(_.simplify)  // clean up anything introduced

        problemState.copy(
            theory = newTheory
        )
    }

    override def name: String = "Simplify Scalar Quantifiers Transformer"
}
