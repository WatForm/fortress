package fortress.transformers

import fortress.tfol._

/** Instantiates quantifiers with all domain elements.
  * This transformation is parameterized by scopes mapping types to sizes.
  * The input theory is required to have no existential quantifiers.
  */
class DomainInstantiationTransformer(scopes: Map[Type, Int]) extends TheoryTransformer {
    override def apply(theory: Theory): Theory = ???
    
    override def getName: String = "Domain Instantiation Transformer"
}
