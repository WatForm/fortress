package fortress.transformers

import fortress.msfol._
import fortress.operations.TheoryOps._
import fortress.modelfind.ProblemState

class SortInferenceTransformer extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf) => {
            val (generalTheory, sortSubstitution) = theory.inferSorts
            // Create new scopes
            val newScopes = for {
                sort <- generalTheory.sorts
                if !sort.isBuiltin
            } yield {
                sort -> scopes(sortSubstitution(sort))
            }
            new ProblemState(generalTheory, newScopes.toMap, skc map (sortSubstitution(_)), skf map (sortSubstitution(_)))
        }
    }
    
    val name: String = "Sort Inference Transformer"
    
}
