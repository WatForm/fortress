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

/** Skolemizes existential quantifiers in the theory.
  * Requires that the theory be in negation normal form.
  */
object SkolemizeTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val forbiddenNames = scala.collection.mutable.Set[String]()
            
            for(sort <- theory.sorts) {
                forbiddenNames += sort.name
            }
            
            for(fdecl <- theory.functionDeclarations) {
                forbiddenNames += fdecl.name
            }
            
            for(constant <- theory.constants) {
                forbiddenNames += constant.name
            }
            
            // TODO: do we need this restriction if Substituter already restricts these inside one term?
            for(axiom <- theory.axioms) {
                forbiddenNames ++= axiom.allSymbols
            }
            
            val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
            
            var resultTheory = theory.withoutAxioms
            val newSkolemConstants = scala.collection.mutable.Set.empty[AnnotatedVar]
            val newSkolemFunctions = scala.collection.mutable.Set.empty[FuncDecl]
            for(axiom <- theory.axioms) {
                val skolemResult = Skolemization.skolemize(axiom, resultTheory.signature, nameGenerator)
                val newAxiom = skolemResult.skolemizedTerm
                newSkolemConstants ++= skolemResult.skolemConstants
                newSkolemFunctions ++= skolemResult.skolemFunctions
                resultTheory = resultTheory.withFunctionDeclarations(skolemResult.skolemFunctions.toList)
                resultTheory = resultTheory.withConstantDeclarations(skolemResult.skolemConstants.toList)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }
            // Function definitions can be skolemized as if each argument was universally quantified
            val functionDefinitions = resultTheory.functionDefinitions
            resultTheory = resultTheory.withoutFunctionDefinitions
            for (fDef <- functionDefinitions) {
                val wrappedTerm = Forall(fDef.argSortedVar, fDef.body)
                val skolemResult = Skolemization.skolemize(wrappedTerm, resultTheory.signature, nameGenerator)
                newSkolemConstants ++= skolemResult.skolemConstants
                newSkolemFunctions ++= skolemResult.skolemFunctions
                resultTheory = resultTheory.withFunctionDeclarations(skolemResult.skolemFunctions.toList)
                resultTheory = resultTheory.withConstantDeclarations(skolemResult.skolemConstants.toList)
                
                // unfold the result term to make the new axiom
                skolemResult.skolemizedTerm match {
                    case Forall(_, newBody) => {
                        val newDef = FunctionDefinition(fDef.name, fDef.argSortedVar, fDef.resultSort, newBody)
                        resultTheory = resultTheory.withFunctionDefinition(newDef) 
                    }
                    case _ => Errors.Internal.impossibleState("Skolemization of Forall did not return Forall.")
                }
            }

            
            val unapply: Interpretation => Interpretation = {
                interp => interp.withoutConstants(newSkolemConstants.toSet).withoutFunctions(newSkolemFunctions.toSet)
            }

            ProblemState(
                resultTheory,
                scopes, skc ++ newSkolemConstants.toSet,
                skf ++ newSkolemFunctions.toSet,
                rangeRestricts,
                unapply :: unapplyInterp,
                distinctConstants
            )
        }
    }
    
    override def name: String = "Skolemize Transformer"
    
}
