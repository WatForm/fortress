package fortress.transformers

import fortress.msfol._
import fortress.operations._

object AxiomatizeFuncDefTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
        val funcDefAxioms: Set[Term] = for( fd <- theory.functionDefinitions ) yield AxiomatizeFuncDef.axiomatize(fd)

        // TODO: add function declaration to theory

        theory.withAxioms(funcDefAxioms).withoutFunctionDefinitions(theory.functionDefinitions)
    }

    override def name: String = "Axiomatize Function Definition Transformer"
}
