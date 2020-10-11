package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
class SimplifyTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  {
        var learnedLiterals : Map[Term,LeafTerm] = Map.empty
        val newAxioms = theory.axioms.map(axiom => {
            val newAxiom = axiom.simplify(learnedLiterals)
            newAxiom match {
                case Not(Eq(t1, t2)) => learnedLiterals = learnedLiterals + (Eq(t1, t2) -> Bottom)
                case Not(App(fname, args)) => learnedLiterals = learnedLiterals + (App(fname, args) -> Bottom)
                case App(_, _) | Eq(_, _) => learnedLiterals = learnedLiterals + (newAxiom -> Top)
                case _ =>
            }
            newAxiom
        }).filter(_ != Top)
        Theory(theory.signature, newAxioms)
    }
    
    override def name: String = "Simplify Transformer"
}
