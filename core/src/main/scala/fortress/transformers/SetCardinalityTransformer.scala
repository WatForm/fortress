package fortress.transformers
import fortress.problemstate.ProblemState
import fortress.data.NameGenerator

object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")

    def generateInPDefinition(nameBase: String, /*a A*/ ): FunctionDefinition = {
        FunctionDefinition(nameGenerator.freshName(nameBase), axy, newSort, IfThenElse(/*a in P?*/, 1, 0))
    }
    
    def generateCardPDefinition(nameBase: String, /*a A*/ ): FunctionDefinition = {
        // for a in A, call inP(a)
    }
    
    
    override def apply(problemState: ProblemState): ProblemState = {
        // get needed functions from operation
        problemState.withFunctionDefinition(generateFunctionDefinition("a"))
    }

// withFunctionDefinition
}
