package fortress.transformers

import fortress.msfol.Signature
import fortress.msfol.Sort
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorEijck
import fortress.transformers._


object ClosureEliminationEijckTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator = {
        return new ClosureEliminatorEijck(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator)
    }

    override def name: String = "Closure Elimination Eijck Transformer"
}