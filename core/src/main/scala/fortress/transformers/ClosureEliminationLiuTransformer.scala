package fortress.transformers

import fortress.msfol.Signature
import fortress.msfol.Sort
import fortress.msfol.Term 
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorLiu
import fortress.transformers._

object ClosureEliminationLiuTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator): ClosureEliminator = {
        return new ClosureEliminatorLiu(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator)
    }

    override def name: String = "Closure Elimination Liu Transformer"
}