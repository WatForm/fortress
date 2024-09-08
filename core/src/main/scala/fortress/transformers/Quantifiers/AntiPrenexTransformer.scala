package fortress.transformers

import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.util.Errors

object AntiPrenexTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        // max alpha renaming is required for anti-prenex
        if (!problemState.flags.haveRunMaxAlphaRenaming) {
            Errors.Internal.preconditionFailed(
                "Max alpha renaming Transformer should be run before AntiPrenexTransformer")
        }

        val theory = problemState.theory
        val newTheory = theory.mapAllTerms(_.antiPrenex)

        problemState
        .withTheory(newTheory)
    }



}
