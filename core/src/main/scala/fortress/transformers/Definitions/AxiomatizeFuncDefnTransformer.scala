package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.problemstate._
import fortress.interpretation._
/*
    Transfer a function definition to a axiom and a function declaration.
    This is just a temporary solution to deal with function definition.
 */

object AxiomatizeFuncDefnTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        
        val theory = problemState.theory

        val funcDefAxioms: Set[Term] = for( fd <- theory.functionDefinitions ) yield {
            Forall(fd.argSortedVar, Eq(App(fd.name, fd.argSortedVar.map(av => av.variable)), fd.body))
        }

        val newFuncDecls: Set[FuncDecl] = for(fd <- theory.functionDefinitions) yield FuncDecl(fd.name, fd.argSortedVar.map(av => av.sort), fd.resultSort)

        val resultTheory = theory
                .withoutFunctionDefinitions(theory.functionDefinitions) // remove function definitions from theory
                .withAxioms(funcDefAxioms)  // add axioms generated by function definitions
                .withFunctionDeclarations(newFuncDecls) // add function declarations generated by function definitions

        val unapply: Interpretation => Interpretation = {
            interp => {
                interp.withoutFunctions(newFuncDecls)
            }
        }

        problemState
        .withTheory(resultTheory)
        .addUnapplyInterp(unapply)
    }


}
