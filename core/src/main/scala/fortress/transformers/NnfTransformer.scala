package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Changes each axiom of the theory into negation normal form. */
object NnfTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
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
        newTheory
    }
    
    override def name: String = "Negation Normal Form Transformer"
}
