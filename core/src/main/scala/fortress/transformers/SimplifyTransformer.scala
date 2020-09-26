package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
class SimplifyTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  theory.mapAxioms(_.simplify)
    
    override def name: String = "Simplify Transformer"
}
