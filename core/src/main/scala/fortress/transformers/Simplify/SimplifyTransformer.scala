package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
object SimplifyTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState =  {
      problemState.copy(theory = problemState.theory.mapAllTerms(_.simplify))
    }


}