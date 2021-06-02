package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Split all conjunct formulas into separate formulas.
  * All other aspects of the theory remain unchanged. */
class SplitConjunctionTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {
        var newAxioms: Set[Term] = Set.empty
        def splitConjunctions(term: Term): Unit = term match {
            case AndList(body) => body.map(t => splitConjunctions(t))
            case _ => newAxioms += term
        }
        theory.axioms.map(splitConjunctions)
    	Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
    }
    
    override def name: String = "Split Conjunction Transformer"
}