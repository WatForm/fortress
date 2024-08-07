package fortress.transformers

import fortress.msfol.Signature
import fortress.msfol.Sort
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorEijck
import fortress.problemstate._
import fortress.transformers._


object ClosureEliminationEijckTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator = {
        new ClosureEliminatorEijck(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator)
    }

}