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

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        val signature = theory.signature
        
        val newCardinalityFunctions = scala.collection.mutable.Set.empty[FuncDecl]
        
        var inApp_function_names: scala.collection.mutable.Map[String, String] = scala.collection.mutable.Map()
        var cardApp_function_names: scala.collection.mutable.Map[String, String] = scala.collection.mutable.Map()
        
        // gathering forbidden names - using the logic from SkolemizeTransformer
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
        def getSort(fname: String): Sort = signature.queryFunction(fname) match {
            case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when getting set cardinatity of it!")
            case Some(Left(FuncDecl(_, sorts, _))) => sorts(0) // we are assuming the function is a unary predicate, in which we want the first element of sorts (there should only be one)
            case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort)(0) // we are assuming the function is a unary predicate, in which we want the first element of params (there should only be one)
        }

        def generateInAppDefinition(name: String, p: String, sort: Sort): FunctionDefinition = {
            // generate a name for inP argument
            val x = nameGenerator.freshName("x")
            val args: Seq[AnnotatedVar] = Seq(AnnotatedVar(Var(x), sort))
            
            // body = ite(p(x), 1, 0)
            val body = IfThenElse(App(p, Seq(Var(x))), IntegerLiteral(1), IntegerLiteral(0))
            
            FunctionDefinition(name, args, IntSort, body)
        }
        
        def generateCardAppDefinition(name: String, pSort: Sort, inP: String, scope: Int): FunctionDefinition = {
            // where inP is the name of the helper function holing ite
            if (inP == ""){
                // if there is no inP function name, something is wrong
                throw Errors.Internal.impossibleState(inP + " has not been defined.")
            }
            // call inP for each element in the relevant domain 
            // ex: P: A-> Bool, call inP for each a:A
            val arguments: Seq[Term] = for (num <- 1 to scope) yield App(inP, DomainElement(num, pSort))
            var body : Term = IntegerLiteral(0)
            
            // add the seperate calls to inP together
            for (arg <- arguments) {
                body = Term.mkPlus(body, arg)
            }
            
            val args: Seq[AnnotatedVar] = Seq()
            FunctionDefinition(name, args, IntSort, body)
        }

        var resultTheory = theory.withoutAxioms // start with a blank theory
        
        // get needed functions from operation
        for(axiom <- theory.axioms) {
            val cardinalityResult = SetCardinalityOperation.cardinality(axiom, inApp_function_names, cardApp_function_names, nameGenerator)

            // passing the generated names back and forth
            inApp_function_names = cardinalityResult.inApp_function_names
            cardApp_function_names = cardinalityResult.cardApp_function_names
            
            // updating axiom
            val newAxiom = cardinalityResult.cardinalityTerm
            resultTheory = resultTheory.withAxiom(newAxiom)
        }
        
        def updateWithResult(funcDefs: Iterable[FunctionDefinition]): Unit = {
            resultTheory = resultTheory.withFunctionDefinitions(funcDefs)
        }
        
        // generate funciton definitions
        // at this point inApp_function_names and cardApp_function_names has the names of all definitions we need to make
        val inAppDefns = scala.collection.mutable.Set[FunctionDefinition]()
        val cardAppDefns = scala.collection.mutable.Set[FunctionDefinition]()
        
        // generate function definitions for inApp
        for ((p, pname) <- inApp_function_names){
            val sort: Sort = getSort(p)
            inAppDefns += generateInAppDefinition(pname, p, sort)
        }
        updateWithResult(inAppDefns)
        
        // generate function definitions for cardApp
        for ((p, pname) <- cardApp_function_names){
            // Precondition check that we have a scope for this method
            Errors.Internal.precondition(scopes.contains(getSort(p)), s"sort in predicate ${p} must be bounded when using set cardinality.")
            val scope = scopes.get(getSort(p))
            cardAppDefns += generateCardAppDefinition(pname, getSort(p), inApp_function_names(p), scope.size)
        }
        updateWithResult(cardAppDefns)
        
        def unapply: Interpretation => Interpretation = {
            interp => interp.withoutFunctionDefinitions(inAppDefns.toSet).withoutFunctionDefinitions(cardAppDefns.toSet)
        }

        //update problem states with theory
        problemState
        .withTheory(resultTheory)
        .addUnapplyInterp(unapply)
    }
}
