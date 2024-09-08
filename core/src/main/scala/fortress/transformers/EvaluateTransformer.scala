package fortress.transformers

import fortress.operations.EvaluationInliner
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/**
  * A transformer that evaluates terms that are independent of the interpretation.
  */
object EvaluateTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        // Evaluate definitions in dependency order to minimize duplicate work
        var theory = problemState.theory
        val inliner = new EvaluationInliner(theory)
        for (defn <- problemState.theory.signature.definitionsInDependencyOrder()) {
            defn match {
                case Left(cDef) =>
                    theory = theory.withoutConstantDefinition(cDef)
                    theory = theory.withConstantDefinition(cDef.mapBody(inliner.naturalRecur))
                case Right(fDef) =>
                    theory = theory.withoutFunctionDefinition(fDef)
                    theory = theory.withFunctionDefinition(fDef.mapBody(inliner.naturalRecur))
            }
            inliner.changeTheory(theory)
        }
        val newAxioms = theory.axioms.map(inliner.naturalRecur)
        val newTheory = theory.copy(axioms = newAxioms)

        problemState
        .withTheory(newTheory)
        .withFlags(problemState.flags.copy(trivialResult = newTheory.checkTrivial))
    }

}
