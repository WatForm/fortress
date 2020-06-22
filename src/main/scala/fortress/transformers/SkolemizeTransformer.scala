package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.Skolemizer
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.modelfind.ProblemState

/** Given a theory, with formulas all in negation normal form, eliminates existential
* quantifiers through skolemization. The resulting theory is equisatisfiable with
* the original.
* Precondition: Input theory is in negation normal form.*/
class SkolemizeTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, unapplyInterp) => {
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
                val skolemizer = new Skolemizer(axiom, resultTheory.signature, nameGenerator)
                val newAxiom = skolemizer.convert()
                newSkolemConstants ++= skolemizer.getSkolemConstants
                newSkolemFunctions ++= skolemizer.getSkolemFunctions
                resultTheory = resultTheory.withFunctionDeclarations(skolemizer.getSkolemFunctions.toList)
                resultTheory = resultTheory.withConstants(skolemizer.getSkolemConstants.toList)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }
            
            ProblemState(resultTheory, scopes, skc ++ newSkolemConstants.toSet, skf ++ newSkolemFunctions.toSet, unapplyInterp)
        }
    }
    
    override def name: String = "Skolemize Transformer"
    
}
