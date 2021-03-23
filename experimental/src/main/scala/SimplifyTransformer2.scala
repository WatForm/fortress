package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
class SimplifyTransformer2 extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  theory.mapAxioms(Simplifier2.simplify(_))
    
    override def name: String = "Simplify Transformer 2"
}
