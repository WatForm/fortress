package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Changes each axiom of the theory into negation normal form.
  * All other aspects of the theory remain unchanged.
  * The resulting theory is equivalent to the first (that is, corresponding formulas
  * are equivalent. */
class NnfTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = theory.mapAxioms(_.nnf)
    
    override def name: String = "Negation Normal Form Transformer"
}
