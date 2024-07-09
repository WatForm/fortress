package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorClaessen
import fortress.problemstate._
import fortress.transformers._


object ClosureEliminationClaessenTransformer extends ClosureEliminationTransformer {
    override def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator = {
        return new ClosureEliminatorClaessen(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator)
    }


}