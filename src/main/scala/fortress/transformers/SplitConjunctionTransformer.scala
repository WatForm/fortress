package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Split all conjunct formulas into separate formulas.
  * All other aspects of the theory remain unchanged. */
class SplitConjunctionTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {
    	val newAxioms = theory.axioms.foldLeft(Seq[Term]())(
    		(axioms, axiom) => axioms ++ (axiom match {
    			case AndList(body) => body.map(t => t)
    			case _ => Seq(axiom)
    		})
    	)
    	Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
    }
    
    override def name: String = "Split Conjunction Transformer"
}