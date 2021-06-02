package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.Skolemization
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation

/** Given a theory, with formulas all in negation normal form, eliminates existential
* quantifiers through skolemization. The resulting theory is equisatisfiable with
* the original.
* Precondition: Input theory is in negation normal form.*/
class SkolemizeTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
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
                resultTheory = resultTheory.withConstants(skolemResult.skolemConstants.toList)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }
            
            val unapply: Interpretation => Interpretation = {
                interp => interp.withoutConstants(newSkolemConstants.toSet).withoutFunctions(newSkolemFunctions.toSet)
            }
            ProblemState(
                resultTheory,
                scopes, skc ++ newSkolemConstants.toSet,
                skf ++ newSkolemFunctions.toSet,
                rangeRestricts,
                unapply :: unapplyInterp
            )
        }
    }
    
    override def name: String = "Skolemize Transformer"
    
}