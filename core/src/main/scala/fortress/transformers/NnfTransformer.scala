package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.util.Errors

/** Changes each axiom of the theory into negation normal form. */
object NnfTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {

        if (problemState.flags.haveRunIfLifting==false) {
            println(s"WARNING: IfLifting Transformer should be run before nnf")
        }
        val theory = problemState.theory
        var newTheory = theory.mapAxioms(_.nnf)

        // We only remove a definition before readding it so all its dependencies are in the sig
        for(cDef <- theory.signature.constantDefinitions){
            newTheory = newTheory.withoutConstantDefinition(cDef)
            newTheory = newTheory.withConstantDefinition(cDef.mapBody(_.nnf))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newTheory = newTheory.withoutFunctionDefinition(fDef)
            newTheory = newTheory.withFunctionDefinition(fDef.mapBody(_.nnf))
        }
        
        problemState.copy(
            theory = newTheory,
            flags = problemState.flags.copy(haveRunNNF = true)
        )
    }
    

}
