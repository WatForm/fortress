package fortress.transformers

import fortress.msfol.Theory
import fortress.operations.{DefinitionInlineHeuristic, DefinitionInliner}
import fortress.problemstate.ProblemState

/**
  * A transformer that inlines some function definitions based on a heuristic.
  */
class InlineDefinitionsTransformer(heuristic: Theory => DefinitionInlineHeuristic) extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        problemState.copy(theory = DefinitionInliner.inline(problemState.theory, heuristic(problemState.theory)))
    }

}
