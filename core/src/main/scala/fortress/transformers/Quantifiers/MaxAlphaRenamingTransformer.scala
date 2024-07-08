package fortress.transformers

import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/**
  * Renames quantified variables in the theory to the maximum extent possible.
  * See MaxAlphaRenaming.
  */
object MaxAlphaRenamingTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = problemState.copy(
        theory = problemState.theory.maxAlphaRenaming,
        flags = problemState.flags.copy(haveRunMaxAlphaRenaming = true),
    )

    override def name: String = "Max Alpha Renaming Transformer"

}
