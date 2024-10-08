package fortress.transformers

import fortress.data.IntSuffixNameGenerator
import fortress.msfol._
import fortress.operations.{Context, QuantifiersToDefinitions}
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.util.Errors

object QuantifiersToDefnsTransformer extends ProblemStateTransformer {



    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val forbiddenNames = scala.collection.mutable.Set[String]()

        for(sort <- theory.sorts) {
            forbiddenNames += sort.name
        }

        for(fdecl <- theory.functionDeclarations) {
            forbiddenNames += fdecl.name
        }

        for(constant <- theory.constantDeclarations) {
            forbiddenNames += constant.name
        }

        val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)

        var resultTheory = theory.withoutAxioms

        val closureFunctions = scala.collection.mutable.Set[FunctionDefinition]()

        def updateResult(result: QuantifiersToDefinitions.Result): Unit = {
            closureFunctions ++= result.definitions
            resultTheory = resultTheory.withFunctionDefinitions(result.definitions)
        }

        for (axiom <- theory.axioms) {
            val result = QuantifiersToDefinitions(axiom, resultTheory.signature, nameGenerator)
            updateResult(result)
            resultTheory = resultTheory.withAxiom(result.resultTerm)
        }

        for (cDef <- theory.constantDefinitions) {
            resultTheory = resultTheory.withoutConstantDefinition(cDef)
            val result = QuantifiersToDefinitions(cDef.body, resultTheory.signature, nameGenerator)
            updateResult(result)
            resultTheory = resultTheory.withConstantDefinition(
                ConstantDefinition(cDef.avar, result.resultTerm))
        }

        for (fDef <- theory.functionDefinitions) {
            // be careful not to apply to the definitions we generated!
            if (!(closureFunctions contains fDef)) {
                resultTheory = resultTheory.withoutFunctionDefinition(fDef)
                val context = Context.empty(resultTheory.signature).stackPush(fDef.argSortedVar)
                val result = QuantifiersToDefinitions(
                    fDef.body, resultTheory.signature, nameGenerator, Some(context))
                updateResult(result)
                resultTheory = resultTheory.withFunctionDefinition(
                    fDef.copy(body = result.resultTerm))
            }
        }

        problemState
        .withTheory(resultTheory)
    }

}
