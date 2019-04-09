package fortress.transformers

import fortress.tfol._

/** Replaces domain elements with distinct constants that simulate them.
  * This transformation is required before sending the theory to an SMT solver.
  */
class DomainEliminationTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = ???
    
    override def getName: String = "Domain Elimination Transformer"
}
