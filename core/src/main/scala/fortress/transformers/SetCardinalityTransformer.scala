package fortress.transformers
import fortress.problemstate.ProblemState
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.data.IntSuffixNameGenerator
import fortress.operations.SetCardinalityOperation
import fortress.util.Errors



object SetCardinalityTransformer extends ProblemStateTransformer {
    println("test in set cardinality transformer")

    override def apply(problemState: ProblemState): ProblemState = {
        Console.println("Set Cardinality apply function called")
        val theory = problemState.theory
        val scopes = problemState.scopes
        val signature = theory.signature
        
        val newCardinalityFunctions = scala.collection.mutable.Set.empty[FuncDecl]
        
        var inApp_function_names: scala.collection.mutable.Map[String, String] = scala.collection.mutable.Map()
        var cardApp_function_names: scala.collection.mutable.Map[String, String] = scala.collection.mutable.Map()
        
        // gathering forbiden names - using the logic from SkolemizeTransformer
        val forbiddenNames = scala.collection.mutable.Set[String]()
        
        for(sort <- theory.sorts) {
            Console.println("epic sort loop")
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
        Console.println("allSymbols seems to be problematic")
        for(axiom <- theory.axioms) {
            forbiddenNames ++= axiom.allSymbols
        }

        val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
        
        Console.println("created name generator")
        // defining helper functions
        def getSort(fname: String): Sort = signature.queryFunction(fname) match {
            case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when getting set cardinatity of it!")
            case Some(Left(FuncDecl(_, sorts, _))) => sorts(0) // we are assuming the function is a unary predicate, in which we want the first element of sorts (there should only be one)
            case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort)(0) // we are assuming the function is a unary predicate, in which we want the first element of params (there should only be one)
        }

        // TODO I want p to be the name, not the App itself
        def generateInAppDefinition(name: String, p: String, sort: Sort): FunctionDefinition = {
            // replace 1 & 0 with number terms. IntegerLiteral
            // generate a name for x
            // App(p, Var(x)) == p(x) basically
            val x = nameGenerator.freshName("x")
            val args: Seq[AnnotatedVar] = Seq(AnnotatedVar(Var(x), sort)) // do we need to add the var to the theory?
            
            val xVar = Var(x)
            val body = IfThenElse(App(p, Seq(xVar)), IntegerLiteral(1), IntegerLiteral(0))
            
            // use the same name for Var(x) and AnnotatedVar(x)
            // arguments to a function definition are a sequence of annotated vars (var + sort)
            // choose some name, sort = sort p takes p: [sort] -> bool
            FunctionDefinition(name, args, IntSort, body)
        }
        
        def generateCardAppDefinition(name: String, pSort: Sort, inP: String, scope: Int): FunctionDefinition = {
            Console.println("generateCardAppDefinition called")
            // where p is the predicate the cardinality is about and inP is the helper function
            if (inP == ""){
                // if there is no inP function name, something is wrong
                // throw error here
            }
        
            // does Domain element index from 0 or 1?
            // * DomainElements are indexed starting with 1. <- taken from DomainElement term
            // to is inclusive
            val arguments: Seq[Term] = for (num <- 1 to scope) yield App(inP, DomainElement(num, pSort))
            var body : Term = IntegerLiteral(0)
            
            for (arg <- arguments) {
                body = Term.mkPlus(body, arg)
            }
            
            val args: Seq[AnnotatedVar] = Seq(/*AnnotatedVar(Var(p), sort) AnnotatedVar(Var(inP), pSort)*/)
            // need to figure out how to pass in the arguments for this function
            // or what the arguments actually are, I think its p, inP, and scope
            FunctionDefinition(name, args, IntSort, body)
        }

        var resultTheory = theory.withoutAxioms // start with a blank theory
        
        // get needed functions from operation
        for(axiom <- theory.axioms) {
            Console.println("main suspicious axiom loop")
            Console.println(resultTheory)
            Console.println(axiom)
            val cardinalityResult = SetCardinalityOperation.cardinality(axiom, inApp_function_names, cardApp_function_names, nameGenerator)
            // passing the generated names back and forth
            inApp_function_names = cardinalityResult.inApp_function_names
            cardApp_function_names = cardinalityResult.cardApp_function_names
            
            // updating axiom
            val newAxiom = cardinalityResult.cardinalityTerm
            resultTheory = resultTheory.withAxiom(newAxiom)
            Console.println(resultTheory)

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
        for ((p, pname) <- inApp_function_names){
            val sort: Sort = getSort(p)
            inAppDefns += generateInAppDefinition(pname, p, sort)
        }
        updateWithResult(inAppDefns)
        Console.println(resultTheory)

        
        // generate function definitions for cardApp
        for ((p, pname) <- cardApp_function_names){
            val scope = scopes(getSort(p))
            cardAppDefns += generateCardAppDefinition(pname, getSort(p), inApp_function_names(p), scope.size)
        }
        updateWithResult(cardAppDefns)
        Console.println(resultTheory)

        
        def unapply: Interpretation => Interpretation = {
            interp => interp.withoutFunctionDefinitions(inAppDefns.toSet).withoutFunctionDefinitions(cardAppDefns.toSet)
        }

        Console.println("returning epic problem state wahoo")
        Console.println(resultTheory)

        //update problem states with theory
        problemState
        .withTheory(resultTheory) // function definitions are in the theory, so we only need to add the theory
        .addUnapplyInterp(unapply)
    }
}
