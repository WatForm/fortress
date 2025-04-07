package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.Skolemization
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate.ProblemState
import fortress.util.Errors
import fortress.operations.TypeChecker

object Skolemize2ndOrderOnlyTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        if(!problemState.flags.constains2ndOrderQuantifiers) problemState
        else {
            val newState = NnfTransformer(IfLiftingTransformer(problemState))
            
            val theory = newState.theory
        
            val nameGenerator = IntSuffixNameGenerator.restrictAllNamesInTheory(theory)
        
            var resultTheory = theory.withoutAxioms
            val newSkolemConstants = scala.collection.mutable.Set.empty[AnnotatedVar]
            val newSkolemFunctions = scala.collection.mutable.Set.empty[FuncDecl]
            
            def updateWithResult(skolemResult: Skolemization.SkolemResult): Unit = {
                newSkolemConstants ++= skolemResult.skolemConstants
                newSkolemFunctions ++= skolemResult.skolemFunctions
                resultTheory = resultTheory.withFunctionDeclarations(skolemResult.skolemFunctions.toList)
                resultTheory = resultTheory.withConstantDeclarations(skolemResult.skolemConstants.toList)
            }

            for(axiom <- theory.axioms) {
                val skolemResult = Skolemization.skolemize2ndOrderOnly(axiom, resultTheory.signature, nameGenerator)
                val newAxiom = skolemResult.skolemizedTerm
                updateWithResult(skolemResult)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }
            
            val unapply: Interpretation => Interpretation = {
                interp => interp.withoutConstants(newSkolemConstants.toSet).withoutFunctions(newSkolemFunctions.toSet)
            }

            val newState2 = problemState
                .withTheory(resultTheory)
                .addSkolemConstants(newSkolemConstants.toSet)
                .addSkolemFunctions(newSkolemFunctions.toSet)
                .addUnapplyInterp(unapply)
                .withFlags(problemState.flags.copy(haveRunSkolemizer = true))

            // Check we were able to actually get rid of all 2nd order quantifiers
            val newState2Typechecked = TypecheckSanitizeTransformer(newState2)
            if(newState2Typechecked.flags.constains2ndOrderQuantifiers) {
                println(newState2Typechecked.theory)
                throw new fortress.util.Errors.UnsupportedFeature("2nd order quantifiers could not all be eliminated - feature is unsupported.")
            } else {
                newState2
            }
        }
    }
    
}
