package fortress.transformers

import fortress.msfol._

class SortInferenceTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    def apply(theory: Theory): Theory = ???
    
    val name: String = "Sort Inference Transformer"
    
}
