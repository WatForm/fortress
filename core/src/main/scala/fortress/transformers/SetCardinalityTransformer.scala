package fortress.transformers
import fortress.problemstate.ProblemState

object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")

    override def apply(problemState: ProblemState): ProblemState = {
        problemState
    }

}
