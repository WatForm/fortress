package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState


/** Changes each axiom of the theory into negation normal form. */
object IfLiftingTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {


        
        val theory = problemState.theory
        var newTheory = theory.mapAxioms(_.iflift)
        // We only remove a definition before readding it so all its dependencies are in the sig
        for(cDef <- theory.signature.constantDefinitions){
            newTheory = newTheory.withoutConstantDefinition(cDef)
            newTheory = newTheory.withConstantDefinition(cDef.mapBody(_.iflift))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newTheory = newTheory.withoutFunctionDefinition(fDef)
            newTheory = newTheory.withFunctionDefinition(fDef.mapBody(_.iflift))
        }
        
        problemState.copy(
            theory = newTheory,
            flags = problemState.flags.copy(containsIte = false)
        )
    }
    
    override def name: String = "IfLifting Transformer"
}
