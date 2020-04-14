package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.ClosureEliminator

import scala.jdk.CollectionConverters._

/** Replaces transitive closure terms with a term representing the application of a new relation
 but with same arguments. **/
class ClosureEliminationTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {

    def this(scopes: java.util.Map[Sort, Integer]) = this({
        val scopes1: Map[Sort, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
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
            val closureEliminator = new ClosureEliminator(axiom, result.signature, scopes, nameGenerator)
            val newAxiom = closureEliminator.convert()
            result = result.withFunctionDeclarations(closureEliminator.getClosureFunctions.toList)
            result = result.withAxioms(closureEliminator.getClosureAxioms.toList)
            result = result.withAxiom(newAxiom)
        }
        
        result
    }
    
    override def name: String = "Closure Elimination Transformer"
    
}