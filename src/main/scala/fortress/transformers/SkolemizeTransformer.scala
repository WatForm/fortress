package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.Skolemizer
import fortress.operations.TermOps._

import scala.jdk.CollectionConverters._

/** Takes a theory, whose formulas are all in negation normal form, and produces
* an equisatisfiable theory whose formulas are still in negation normal form and
* contain no existential quantifiers.
* Prenex normal form is preserved.
* Scopes are preserved. */
class SkolemizeTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {
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
        
        var result = theory.withoutAxioms
        for(axiom <- theory.axioms) {
            val skolemizer = new Skolemizer(axiom, result.signature, nameGenerator)
            val newAxiom = skolemizer.convert()
            result = result.withFunctionDeclarations(skolemizer.getSkolemFunctions.toList)
            result = result.withConstants(skolemizer.getSkolemConstants.toList)
            result = result.withAxiom(newAxiom)
        }
        
        result;
    }
    
    override def name: String = "Skolemize Transformer"
    
}
