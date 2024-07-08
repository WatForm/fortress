package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.{ClosureEliminator, ClosureEliminatorIterative}
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate._

/** Replaces transitive closure terms with a term representing the application of a new relation
 but with same arguments. **/
object ClosureEliminationIterativeTransformer extends ClosureEliminationTransformer  {

    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorIterative(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator)
    }
    
    override def name: String = "Closure Elimination Iterative Transformer"
    
}