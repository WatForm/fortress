package fortress.transformers

import fortress.msfol._
import fortress.operations._

/*
    Transfer a function definition to a axiom and a function declaration.
    This is just a temporary solution to deal with function definition.
 */

object AxiomatizeFuncDefTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
        val funcDefAxioms: Set[Term] = for( fd <- theory.functionDefinitions ) yield {
            Forall(fd.argSortedVar, Eq(App(fd.name, fd.argSortedVar.map(av => av.variable)), fd.body))
        }

        val newFuncDecls: Set[FuncDecl] = for(fd <- theory.functionDefinitions) yield FuncDecl(fd.name, fd.argSortedVar.map(av => av.sort), fd.resultSort)

        theory
            .withoutFunctionDefinitions(theory.functionDefinitions) // remove function definitions from theory
            .withAxioms(funcDefAxioms)  // add axioms generated by function definitions
            .withFunctionDeclarations(newFuncDecls) // add function declarations generated by function definitions
    }

    override def name: String = "Axiomatize Function Definition Transformer"
}
