package fortress.transformers

import fortress.tfol._

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
class SimplifyTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  {
        val newAxioms = theory.axioms.map(_.simplify)
        theory.withoutAxioms
            .withAxioms(newAxioms)
    }
    
    override def name: String = "Simplify Transformer"
}
