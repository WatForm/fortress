package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.ClosureEliminator

import scala.jdk.CollectionConverters._

/** Replaces transitive closure terms with a term representing the application of a new relation
 but with same arguments. **/
class ClosureEliminationTransformer extends ProblemTransformer {
    override def apply(problem: Problem): Problem = problem match {
        case Problem(theory, scopes) => {
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
            
            val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
            
            var result = theory.withoutAxioms
            for(axiom <- theory.axioms) {
                val closureEliminator = new ClosureEliminator(axiom, result.signature, scopes, nameGenerator)
                val newAxiom = closureEliminator.convert()
                result = result.withFunctionDeclarations(closureEliminator.getClosureFunctions.toList)
                result = result.withAxioms(closureEliminator.getClosureAxioms.toList)
                result = result.withAxiom(newAxiom)
            }
            
            Problem(result, scopes)
        }
    }
    
    override def name: String = "Closure Elimination Transformer"
    
}