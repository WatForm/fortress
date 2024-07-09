package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged.
  *
  * This variant removes the simplification of equality formulas between two domain constants
  * using the fact that the the domain constants were not equal because in the "collapsing constants"
  * approach for solving with non-exact scope, constants are no longer distinct.
  * */

object SimplifyConstantsNotDistinctTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState =  {
      problemState.copy(
        theory = problemState.theory.mapAllTerms(SimplifierConstantsNotDistinct
          .simplify)
      )
    }
    

}
