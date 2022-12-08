package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorVakili
import fortress.problemstate._
import fortress.transformers._

object ClosureEliminationVakiliTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort,Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorVakili(topLevelTerm, signature, scopes, nameGen)
    }

    override def name: String = "Closure Elimination Vakili Transformer"
}