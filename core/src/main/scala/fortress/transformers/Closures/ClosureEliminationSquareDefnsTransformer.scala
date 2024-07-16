package fortress.transformers

import fortress.data.NameGenerator
import fortress.msfol._
import fortress.operations.{ClosureEliminator, ClosureEliminatorSquareDefns}
import fortress.problemstate._

object ClosureEliminationSquareDefnsTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort,Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorSquareDefns(topLevelTerm, signature, scopes, nameGen)
    }

}