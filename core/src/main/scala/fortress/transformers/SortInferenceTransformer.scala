package fortress.transformers

import fortress.msfol._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.sortinference._

/** Infers new sorts within the theory.
  * If no new sorts are found, returns the original theory.
  */
object SortInferenceTransformer extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val (generalTheory, sortSubstitution) = theory.inferSorts
            // Create new scopes
            val newScopes = for {
                sort <- generalTheory.sorts
                if !sort.isBuiltin && scopes.contains(sort)
            } yield {
                sort -> scopes(sortSubstitution(sort))
            }
            val unapply: Interpretation => Interpretation = _.applySortSubstitution(sortSubstitution)

            ProblemState(generalTheory, newScopes.toMap, skc map (sortSubstitution(_)), skf map (sortSubstitution(_)), rangeRestricts, unapply :: unapplyInterp, distinctConstants)
        }
    }
    
    val name: String = "Sort Inference Transformer"
    
}
