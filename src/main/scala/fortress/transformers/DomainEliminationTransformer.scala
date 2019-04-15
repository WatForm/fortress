package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._

/** Replaces domain elements with distinct constants that simulate them.
  * This transformation is required before sending the theory to an SMT solver.
  */
class DomainEliminationTransformer(scopes: Map[Type, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Type, Integer]) = this({
        val scopes1: Map[Type, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = ???
    
    override def getName: String = "Domain Elimination Transformer"
}
