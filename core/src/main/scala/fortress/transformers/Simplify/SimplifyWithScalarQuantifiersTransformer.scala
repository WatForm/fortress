package fortress.transformers

import fortress.operations._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.util.Errors

object SimplifyWithScalarQuantifiersTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        // must have done as much nnf as possible
        if (!problemState.flags.haveRunNNF) {
            Errors.Internal.preconditionFailed(
                "NNF Transformer should be run before SimplifyWithScalarQuantifiersTransformer")
        }
        // max alpha renaming is required for anti-prenex
        if (!problemState.flags.haveRunMaxAlphaRenaming) {
            Errors.Internal.preconditionFailed(
                "Max alpha renaming Transformer should be run before SimplifyWithScalarQuantifiersTransformer")
        }

        val newTheory = problemState.theory
            .mapAllTerms(_.simplify)  // necessary before ScalarQuantifierSimplifier
            .mapAllTerms(_.antiPrenex) // push in as far as possible for a better shot at elimination terms
            .mapAllTerms(_.partialPrenex) // pull back so we can see all the elimination terms
            .mapAllTerms(ScalarQuantifierSimplifier.simplify)
            .mapAllTerms(_.simplify)  // clean up anything introduced

        problemState.withTheory(newTheory)
    }



}
