package fortress.transformers
import fortress.problemstate.ProblemState
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.data.IntSuffixNameGenerator
import fortress.operations.SetCardinality
import fortress.util.Errors



object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality")

    override def apply(problemState: ProblemState): ProblemState = {

        val theory = problemState.theory
        val scopes = problemState.scopes
        val signature = problemState.signature
        
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
        
        // defining helper functions
        // it is possible you can just do some sort of variation of .sort on predicates
        def getSort(fname: String): Seq[Sort] = signature.queryFunction(fname) match {
            // need to edit this to match set cardinality, I think getting rid of the drop(2) perhaps?
            case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when getting set cardinatity of it!")
            case Some(Left(FuncDecl(_, sorts, _))) => sorts.drop(2).toList
            case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort).drop(2).toList
        }

        def generateInAppDefinition(name: String, p: App): FunctionDefinition = {
            val body = IfThenElse(p(x), 1, 0)
            FunctionDefinition(name, /*todo, x?*/ term.arguments, IntSort, body)
        }
        
        def generateCardAppDefinition(name: String, sort: Sort, inP: Var, scope: Int): FunctionDefinition = {
            if (inP == ""){
                // if there is no inP function name, something is wrong
                // throw error here
            }
            
            // what type is the function USE (not definition, usage)
            // for a in A, call inP(a)
            
            //val body2 = y(DomainElement(0, f)) + y(DomainElement(0, f)) + .... 
            // where y = function we just defined, we will know the namne of y based on p #(p) -> this function
            
            //val function2 = FuncDecl(...) // cardP: inp(a1) SUM inp(a2) SUM inp(a3) etc (for all ax in A) // does not take any arguments, applies the first function to all domain elements
            
            // do the SUM thing with a for loop
            // term = first one
            // then loop through the rest with term SUM next
            // return term
            
            val arguments: Seq[Term] = for (num <- scope) yield inP(DomainElement(num, p))
            val body = AndList(arguments)
            
            // need to figure out how to pass in the arguments for this function
            // or what the arguments actually are, I think its p, inP, and scope
            FunctionDefinition(name, /*todo, x?*/ term.arguments, Int, body)
        }

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
            val scope = scopes(getSort(name).head)
            cardAppDefns += generateCardAppDefinition(name, getSort(name), inApp_function_names.get(app), scope.size)
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
