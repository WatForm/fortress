package fortress.transformers

import fortress.msfol._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate.ProblemState
import fortress.sortinference._

/** Infers new sorts within the theory.
  * If no new sorts are found, returns the original theory.
  */
object SortInferenceTransformer extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        
        val (generalTheory, sortSubstitution) = theory.inferSorts
        // Create new scopes
        val newScopes = for {
            sort <- generalTheory.sorts
            if !sort.isBuiltin && scopes.contains(sort)
        } yield {
            sort -> scopes(sortSubstitution(sort))
        }
        val unapply: Interpretation => Interpretation = _.applySortSubstitution(sortSubstitution)

        // ProblemState(generalTheory, newScopes.toMap, skc map (sortSubstitution(_)), skf map (sortSubstitution(_)), rangeRestricts, unapply :: unapplyInterp, distinctConstants)
        problemState.copy(
            theory = generalTheory,
            scopes = newScopes.toMap,
            skolemConstants = problemState.skolemConstants map (sortSubstitution(_)),
            skolemFunctions = problemState.skolemFunctions map (sortSubstitution(_)),
            unapplyInterp = unapply :: problemState.unapplyInterp,
        )
    }
    
    val name: String = "Sort Inference Transformer"
    
}
