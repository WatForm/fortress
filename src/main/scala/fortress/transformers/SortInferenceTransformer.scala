package fortress.transformers

import fortress.msfol._

import scala.collection.immutable.Seq

class SortInferenceTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    def apply(theory: Theory): Theory = ???
    
    val name: String = "Sort Inference Transformer"
    
}
