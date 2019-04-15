package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._

/** Introduces (quantifier-free) range formulas restricting the ranges of
  * function applications and constants.
  * This transformation is parameterized by scopes mapping types to sizes.
  * Performs a low amount of symmetry breaking.
  * The input theory must be quantifier-free.
  * It is required that domain elements must be permutable within the input theory
  * (for example, if a the theory was the result of instantiating a theory that had
  * no explicit domain elements).
  */
class RangeFormulaTransformer(scopes: Map[Type, Int]) extends TheoryTransformer {
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Type, Integer]) = this({
        val scopes1: Map[Type, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = ???
    
    override def getName: String = "Range Formula Transformer (Low Sym)"
}
