package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._

/** Changes each axiom of the theory into negation normal form.
  * All other aspects of the theory remain unchanged.
  * The resulting theory is equivalent to the first (that is, corresponding formulas
  * are equivalent. */
class NnfTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
        val newAxioms = theory.axioms map (_.nnf)
        theory.withoutAxioms
            .withAxioms(newAxioms)
    }
    
    override def name: String = "Negation Normal Form Transformer"
}
