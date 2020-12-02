package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._

class ScopeSubtypeTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  {
        val scopeSubtypePreds = theory.sorts.map(sort => {
            val predName = ScopeSubtype.subtypePred(sort)
            val predDecl = FuncDecl(predName, sort, BoolSort)
            predDecl
        })
        theory
            .withFunctionDeclarations(scopeSubtypePreds)
            .mapAxioms(ScopeSubtype.addBoundsPredicates(_))
    }
    
    override def name: String = "Scope Subtype Transformer"
}
