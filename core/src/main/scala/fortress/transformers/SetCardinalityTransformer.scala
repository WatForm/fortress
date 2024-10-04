package fortress.transformers
import fortress.problemstate.ProblemState

object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")

    def generateInPDefinition(name: String, p: App): FunctionDefinition = {
        val body = IfThenElse(p(x), 1, 0)
        FunctionDefinition(name, /*todo, x?*/, IntSort, body)
    }
    
    def generateCardPDefinition(nameBase: String, /*a A*/ ): FunctionDefinition = {
        // for a in A, call inP(a)
    }
    
    
    override def apply(problemState: ProblemState): ProblemState = {

        val theory = problemState.theory
        val newCardinalityFunctions = scala.collection.mutable.Set.empty[FuncDecl]


        def updateWithResult(cardinalityResult: Skolemization.SkolemResult): Unit = {
            newCardinalityFunctions ++= cardinalityResult.cardinalityFunctions
            theory = theory.withFunctionDeclarations(cardinalityResult.cardinalityFunctions.toList) // note we are NOT using declarations
        }
        
        // get needed functions from operation
        for(axiom <- theory.axioms) { // on a per axiom basis?
            val cardinalityResult = SetCardinality.cardinality(axiom)
            
            // keep track of kept names somehow
        }
        // generate funciton definitions
        
        // update theory
        val newAxiom = cardinalityResult.cardinalityTerm
        updateWithResult(cardinalityResult)
        theory = theory.withAxiom(newAxiom)
            
        //update problem states with theory
        
        // need to be careful/do some research here to ADD not REPLACE function definitions
        // double check with verus add - does with replace all function definitions? If not might want to add an addFunctionDefinitions
        problemState
        .withTheory(theory)
        .withFunctionDefinition(generateFunctionDefinition("a"))
        .addUnapplyInterp(unapply)// todo
    }
}

/*
// potentially useful - Seq(x,y).map(_.of(sort))
            
            // we need to DECLARE the function (funcdecl) and DEFINE the function seperately
            val body1 = IfThenElse(p(x), 1, 0)
            FunctionDefinition(name, variable, body) // todo, need to get the scope of f (p: f->Bool) and pass that to the function
            val function1= FuncDecl(...) // inP: ite(inA(a), 1, 0) 1 argument, a
            cardinalityFunctions += function1
            
            val body2 = y(DomainElement(0, f)) + y(DomainElement(0, f)) + .... 
            // where y = function we just defined, we will know the namne of y based on p #(p) -> this function
            
            val function2 = FuncDecl(...) // cardP: inp(a1) SUM inp(a2) SUM inp(a3) etc (for all ax in A) // does not take any arguments, applies the first function to all domain elements
            ardinalityFunctions += function2
            function2 // this is the term we want to replace #(p) with
            
            // #
            
            
            // Type - type of argument to the cardinality operator
            // #(P) - p has a sort f-> bool
            // sort I want for ina -> f
            // inA is an application, inA is an app for the argument a
            // where does ina come from? comes from portus, not gauranteed to exist in fortress
            // how do I know what to enumerate ina over? all the domain elements in the sort f
                // class called domainElement
*/