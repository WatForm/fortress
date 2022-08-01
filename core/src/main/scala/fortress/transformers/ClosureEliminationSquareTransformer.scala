package fortress.transformers

import fortress.data.NameGenerator
import fortress.msfol._
import fortress.operations.{ClosureEliminator, ClosureEliminatorSquare}

object ClosureEliminationSquareTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort,Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorSquare(topLevelTerm, signature, scopes, nameGen)
    }

    override def name: String = "Closure Elimination Square Transformer"
}