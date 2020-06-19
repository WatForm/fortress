package fortress.transformers

import fortress.msfol._
import fortress.operations.TheoryOps._

class SortInferenceTransformer extends ProblemTransformer {
        
    def apply(problem: Problem): Problem = problem match {
        case Problem(theory, scopes) => {
            val (generalTheory, sortSubstitution) = theory.inferSorts
            // Create new scopes
            val newScopes = for {
                sort <- generalTheory.sorts
                if !sort.isBuiltin
            } yield {
                sort -> scopes(sortSubstitution(sort))
            }
            Problem(generalTheory, newScopes.toMap)
        }
    }
    
    val name: String = "Sort Inference Transformer"
    
}
