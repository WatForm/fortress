package fortress.transformers

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
    override def apply(theory: Theory): Theory = ???
    
    override def getName: String = "Range Formula Transformer (Low Sym)"
}
