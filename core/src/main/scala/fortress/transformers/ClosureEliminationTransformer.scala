package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation

/** Replaces transitive closure terms with a term representing the application of a new relation
 but with same arguments. **/
class ClosureEliminationTransformer extends ProblemStateTransformer {
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
            
            val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
            
            var resultTheory = theory.withoutAxioms
            for(axiom <- theory.axioms) {
                val closureEliminator = new ClosureEliminator(axiom, resultTheory.signature, scopes, nameGenerator)
                val newAxiom = closureEliminator.convert()
                resultTheory = resultTheory.withFunctionDeclarations(closureEliminator.getClosureFunctions.toList)
                resultTheory = resultTheory.withAxioms(closureEliminator.getClosureAxioms.toList)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }
            
            ProblemState(resultTheory, scopes, skc, skf, rangeRestricts, unapplyInterp)
        }
    }
    
    override def name: String = "Closure Elimination Transformer"
    
}