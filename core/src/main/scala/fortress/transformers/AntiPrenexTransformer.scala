package fortress.transformers

import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

object AntiPrenexTransformer extends ProblemStateTransformer {

    override def name: String = "AntiPrenexTransformer"

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        var newTheory = theory.mapAllTerms(_.antiPrenex)

        // We only remove a definition before readding it so all its dependencies are in the sig
        for(cDef <- theory.signature.constantDefinitions){
            newTheory = newTheory.withoutConstantDefinition(cDef)
            newTheory = newTheory.withConstantDefinition(cDef.mapBody(_.antiPrenex))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newTheory = newTheory.withoutFunctionDefinition(fDef)
            newTheory = newTheory.withFunctionDefinition(fDef.mapBody(_.antiPrenex))
        }

        problemState.copy(
            theory = newTheory,
            flags = problemState.flags,
        )
    }

}
