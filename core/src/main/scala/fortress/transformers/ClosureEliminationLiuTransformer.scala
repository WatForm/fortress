package fortress.transformers

import fortress.msfol.Signature
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorLiu
import fortress.transformers._

object ClosureEliminationLiuTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorLiu(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator)
    }

    override def name: String = "Closure Elimination Liu Transformer"
}