package fortress.transformers
import fortress.problemstate.ProblemState
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.data.IntSuffixNameGenerator
import fortress.operations.SetCardinality



object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")

    def generateInAppDefinition(name: String, p: App): FunctionDefinition = {
        // val body = IfThenElse(p(x), 1, 0)
        // FunctionDefinition(name, /*todo, x?*/, IntSort, body)
    }
    
    def generateCardAppDefinition(name: String, p: App): FunctionDefinition = {
        // for a in A, call inP(a)
    }
    
    
    override def apply(problemState: ProblemState): ProblemState = {

        val theory = problemState.theory
        val newCardinalityFunctions = scala.collection.mutable.Set.empty[FuncDecl]
        
        var inApp_function_names: scala.collection.mutable.Map[App, String] = scala.collection.mutable.Map()
        var cardApp_function_names: scala.collection.mutable.Map[App, String] = scala.collection.mutable.Map()
        
        // gathering forbiden names - using the logic from SkolemizeTransformer
        val forbiddenNames = scala.collection.mutable.Set[String]()
        
        for(sort <- theory.sorts) {
            forbiddenNames += sort.name
        }
        
        for(fdecl <- theory.functionDeclarations) {
            forbiddenNames += fdecl.name
        }
        
        for(constant <- theory.constantDeclarations) {
            forbiddenNames += constant.name
        }

        for(cDef <- theory.constantDefinitions){
            forbiddenNames += cDef.name
        }

        for(fDef <- theory.functionDefinitions){
            forbiddenNames += fDef.name
        }
        
        // TODO: do we need this restriction if Substituter already restricts these inside one term?
        for(axiom <- theory.axioms) {
            forbiddenNames ++= axiom.allSymbols
        }

        val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)

        var resultTheory = theory.withoutAxioms // start with a blank theory
        
        // get needed functions from operation
        for(axiom <- theory.axioms) {
            val cardinalityResult = SetCardinality.cardinality(axiom, inApp_function_names, cardApp_function_names, nameGenerator)
            // passing the generated names back and forth
            inApp_function_names = cardinalityResult.inApp_function_names
            cardApp_function_names = cardinalityResult.cardApp_function_names
            
            // updating axiom
            val newAxiom = cardinalityResult.cardinalityTerm
            resultTheory = resultTheory.withAxiom(newAxiom)
        }
        
        // todo - may not need to be it's own function
        def updateWithResult(funcDefs: Iterable[FunctionDefinition]): Unit = {
            resultTheory = resultTheory.withFunctionDefinitions(funcDefs)
        }
        
        // generate funciton definitions
        // at this point inApp_function_names and cardApp_function_names has all the names of definitions we need to make
        val inAppDefns = scala.collection.mutable.Set[FunctionDefinition]()
        val cardAppDefns = scala.collection.mutable.Set[FunctionDefinition]()
        
        // generate function definitions for inApp
        for ((app, name) <- inApp_function_names){
            inAppDefns += generateInAppDefinition(name, app)
        }
        updateWithResult(inAppDefns)
        
        // generate function definitions for cardApp
        for ((app, name) <- cardApp_function_names){
            cardAppDefns += generateCardAppDefinition(name, app)
        }
        updateWithResult(cardAppDefns)
        
        def unapply: Interpretation => Interpretation = {
            interp => interp.withoutFunctionDefinitions(inAppDefns.toSet).withoutFunctionDefinitions(cardAppDefns.toSet)
        }

        //update problem states with theory
        problemState
        .withTheory(resultTheory) // function definitions are in the theory, so we only need to add the theory
        .addUnapplyInterp(unapply)
    }
}
