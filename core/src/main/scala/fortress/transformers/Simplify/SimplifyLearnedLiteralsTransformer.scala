package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.problemstate.ProblemState

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged. */
class SimplifyLearnedLiteralsTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState =  {
        val theory = problemState.theory
        var learnedLiterals : Map[Term,LeafTerm] = Map.empty
        var newAxioms = theory.axioms.map(axiom => {
            val newAxiom = axiom.simplifyWithLearnedLiterals(learnedLiterals)
            newAxiom match {
                case Not(Eq(t1, t2)) => learnedLiterals = learnedLiterals + (Eq(t1, t2) -> Bottom) + (Eq(t2, t1) -> Bottom)
                case Not(App(fname, args)) => learnedLiterals = learnedLiterals + (App(fname, args) -> Bottom)
                case Eq(t1, t2) => learnedLiterals = learnedLiterals + (newAxiom -> Top) + (Eq(t2, t1) -> Top)
                case App(_, _) => learnedLiterals = learnedLiterals + (newAxiom -> Top)
                case _ =>
            }
            newAxiom
        }).filter(_ != Top)
        var numLiterals = 0
        while (numLiterals != learnedLiterals.size) {
            numLiterals = learnedLiterals.size
            newAxioms = newAxioms.map(axiom => axiom match {
                case App(_, _) | Eq(_, _) | Not(App(_, _)) | Not(Eq(_, _)) => axiom
                case _ => {
                    val newAxiom = axiom.simplifyWithLearnedLiterals(learnedLiterals)
                    newAxiom match {
                        case Not(Eq(t1, t2)) => learnedLiterals = learnedLiterals + (Eq(t1, t2) -> Bottom) + (Eq(t2, t1) -> Bottom)
                        case Not(App(fname, args)) => learnedLiterals = learnedLiterals + (App(fname, args) -> Bottom)
                        case Eq(t1, t2) => learnedLiterals = learnedLiterals + (newAxiom -> Top) + (Eq(t2, t1) -> Top)
                        case App(_, _)  => learnedLiterals = learnedLiterals + (newAxiom -> Top)
                        case _ =>
                    }
                    newAxiom
                }
            }).filter(_ != Top)
        }


        // Theory(theory.signature, newAxioms)
        problemState.copy(
            theory = Theory(theory.signature, newAxioms),
        )
    }

    override def name: String = "Simplify Transformer"
}
