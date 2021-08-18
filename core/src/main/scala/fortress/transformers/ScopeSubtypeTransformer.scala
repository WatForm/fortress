package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
class ScopeSubtypeTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  {
        val scopeSubtypePreds = theory.sorts.map(sort => {
            val predName = ScopeSubtype.subtypePred(sort)
            val predDecl = FuncDecl(predName, sort, BoolSort)
            predDecl
        })

        // Have to say the subtypes are nonempty
        val antiVacuityAxioms = theory.sorts.map(sort => Exists(Var("x") of sort, App(ScopeSubtype.subtypePred(sort), Var("x"))))

        // Constants and functions must have ranges in the subtypes
        val constantAxioms = for (av <- theory.constants) yield App(ScopeSubtype.subtypePred(av.sort), av.variable)
        val functionAxioms = for {
            fdecl <- theory.functionDeclarations
            if !fdecl.resultSort.isBuiltin
        } yield {

            val argsAnnotated = fdecl.argSorts.zipWithIndex.map{case (sort, index) => Var(s"x_${sort}_${index}") of sort}
            val outputPred = ScopeSubtype.subtypePred(fdecl.resultSort)
            // We don't need to check that the inputs are in the subtypes, such inputs don't have any affect on the formulas
            Forall(argsAnnotated, App(outputPred, App(fdecl.name, argsAnnotated.map(_.variable))))
        }

        theory
            .withFunctionDeclarations(scopeSubtypePreds)
            .mapAxioms(ScopeSubtype.addBoundsPredicates)
            .withAxioms(antiVacuityAxioms)
            .withAxioms(constantAxioms)
            .withAxioms(functionAxioms)
    }
    
    override def name: String = "Scope Subtype Transformer"
}
