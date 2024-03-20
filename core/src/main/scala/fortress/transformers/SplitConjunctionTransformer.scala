package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Splits all top-level conjunct formulas into separate formulas. */
object SplitConjunctionTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        var newAxioms: Set[Term] = Set.empty
        def splitConjunctions(term: Term): Unit = term match {
            case AndList(body) => body.map(t => splitConjunctions(t))
            case _ => newAxioms += term
        }
        theory.axioms.map(splitConjunctions)
    	val newTheory = Theory(theory.signature, newAxioms)

        problemState.copy(
            theory = newTheory
        )
    }
    
    override def name: String = "Split Conjunction Transformer"
}