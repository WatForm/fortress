
import fortress.msfol._
import fortress.transformers._

// Separate trait to emphasize that this is not the main use of ProblemStateTransformer
// This is mostly here to facilitate simpler unit tests
class TheoryApplication(baseTransformer: ProblemStateTransformer) extends TheoryTransformer {
    def apply(theory: Theory): Theory = baseTransformer.apply(ProblemState(theory)).theory

    def apply(theory: Theory, scopes: Map[Sort, Scope]): Theory = baseTransformer.apply(ProblemState(theory, scopes)).theory

    override def name: String = baseTransformer.name
}