package fortress.transformers
import fortress.problemstate.ProblemState
import fortress.data.NameGenerator

object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")


    // do we need to do these here or in operations?
    def generateInPDefinition(nameBase: String, /*a A*/ ): FunctionDefinition = {
        FunctionDefinition(nameGenerator.freshName(nameBase), axy, newSort, IfThenElse(/*a in P?*/, 1, 0))
    }
    
    def generateCardPDefinition(nameBase: String, /*a A*/ ): FunctionDefinition = {
        // for a in A, call inP(a)
    }
    
    
    override def apply(problemState: ProblemState): ProblemState = {

        val theory = problemState.theory
        val newCardinalityFunctions = scala.collection.mutable.Set.empty[FuncDecl]


        def updateWithResult(cardinalityResult: Skolemization.SkolemResult): Unit = {
            newCardinalityFunctions ++= cardinalityResult.cardinalityFunctions
            theory = theory.withFunctionDeclarations(cardinalityResult.cardinalityFunctions.toList)
        }
        
        // get needed functions from operation
        for(axiom <- theory.axioms) { // on a per axiom basis?
            val cardinalityResult = SetCardinality.cardinality(axiom)
            
            // use result to make functions?
            
            // update theory
            val newAxiom = cardinalityResult.cardinalityTerm
            updateWithResult(cardinalityResult)
            theory = theory.withAxiom(newAxiom)
        }
        
        //update problem states with theory
        problemState.withFunctionDefinition(generateFunctionDefinition("a"))
        
        problemState
        .withTheory(theory)
        .addSkolemFunctions(newCardinalityFunctions.toSet)
        .addUnapplyInterp(unapply)// todo
    }
}