package fortress.operations

import fortress.util.Errors
import fortress.msfol._
import fortress.data._
import fortress.msfol.DSL._

case class TypeCheckResult(
    sanitizedTerm: Term,
    sort: Sort,
    containsConnectives: Boolean,
    containsQuantifiers: Boolean,
    containsItes: Boolean,
    containsExists: Boolean,
)
/** Given a signature and a term, typechecks the term with respect to the signature.
 * Returns a TypeCheckResult containing the sort of the term, AND a new term
 * that is equal to the old term but with instances of Eq replaced with Iff
 * when comparing Bool sorts. Such a term is called "sanitized". */
class TypeChecker(signature: Signature) extends TermVisitorWithTypeContext[TypeCheckResult](signature) {

    override def visitTop(): TypeCheckResult =
        TypeCheckResult(
            sanitizedTerm = Top, 
            sort = BoolSort,
            containsConnectives = false, 
            containsQuantifiers = false, 
            containsItes = false,
            containsExists = false
        )
        
    override def visitBottom(): TypeCheckResult =
        TypeCheckResult(
            sanitizedTerm = Bottom, 
            sort = BoolSort, 
            containsConnectives = false, 
            containsQuantifiers = false, 
            containsItes = false,
            containsExists = false
        )
    
    override def visitVar(variable: Var): TypeCheckResult = {
        // Check variable is not an already declared function symbol
        // This must be done even with a consistent signature
        if(signature hasFuncDeclWithName variable.name) {
            throw new TypeCheckException.NameConflict("Variable or constant name " + variable.name + " conflicts with existing function symbol")
        }

        if(signature hasFuncDefWithName variable.name) {
            // zero-arity defined functions are allowed in smtlib
            val fDef = signature.queryFunctionDefinition(variable.name)
            throw new TypeCheckException.NameConflict("Variable or constant name " + variable.name + " conflicts with existing function symbol")
        }
        
        // Check variable is not an already declared sort symbol
        if(signature hasSortWithName variable.name) {
            throw new TypeCheckException.NameConflict("Variable or constant name " + variable.name + " conflicts with existing sort symbol")
        }
        
        val sortMaybe = lookupSort(variable)
        if(sortMaybe.isEmpty) {
            throw new TypeCheckException.UndeterminedSort("Could not determine sort of variable " + variable.name)
        }
        
        TypeCheckResult(
            sanitizedTerm = variable, 
            sort = sortMaybe.get,
            containsConnectives = false, 
            containsQuantifiers = false , 
            containsItes = false,
            containsExists = false,
        )
    }
    
    override def visitNot(not: Not): TypeCheckResult = {
        val bodyResult = visit(not.body)
        if(bodyResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Argument of negation is of sort " + bodyResult.sort.name + " in " + not.toString)
        }
        TypeCheckResult(
            sanitizedTerm = Not(bodyResult.sanitizedTerm), 
            sort = BoolSort,
            containsConnectives = true, 
            containsQuantifiers = bodyResult.containsQuantifiers,
            containsItes = bodyResult.containsItes,
            containsExists = bodyResult.containsExists
        )
    }
    
    override def visitAndList(andList: AndList): TypeCheckResult = {
        val results = andList.arguments.map(visit)
        for(result <- results) {
            if(result.sort != BoolSort) {
                throw new TypeCheckException.WrongSort("Expected sort Bool but was " + result.sort.name + " in " + andList.toString)
            }
        }
        TypeCheckResult(
            sanitizedTerm = AndList(results.map(_.sanitizedTerm)), 
            sort = BoolSort,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers),
            containsItes = results.exists(_.containsItes),
            containsExists = results.exists(_.containsExists)
        )
    }
    
    override def visitOrList(orList: OrList): TypeCheckResult = {
        val results = orList.arguments.map(visit)
        for(result <- results) {
            if(result.sort != BoolSort) {
                throw new TypeCheckException.WrongSort("Expected sort Bool but was " + result.sort.name + " in " + orList.toString)
            }
        }
        TypeCheckResult(
            sanitizedTerm = OrList(results.map(_.sanitizedTerm)), 
            sort = BoolSort,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers),
            containsItes = results.exists(_.containsItes),
            containsExists = results.exists(_.containsExists)
        )
    }
    
    override def visitDistinct(distinct: Distinct): TypeCheckResult = {
        val results: Seq[TypeCheckResult] = distinct.arguments.map(visit)
        
        // Check sorts all the same
        val sorts: Seq[Sort] = results.map(_.sort)
        if(sorts.distinct.size > 1) {
            throw new TypeCheckException.WrongSort("Arguments of multiple sorts " + sorts.toString + " in " + distinct.toString)
        }
        
        TypeCheckResult(
            sanitizedTerm = Distinct(results.map(_.sanitizedTerm)), 
            sort = BoolSort,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers),
            containsItes = results.exists(_.containsItes),
            containsExists = results.exists(_.containsExists)
        )
    }
    
    override def visitImplication(imp: Implication): TypeCheckResult = {
        val leftResult = visit(imp.left)
        val rightResult = visit(imp.right)
        
        if(leftResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected sort Bool but was " + leftResult.sort.name + " in " + imp.toString)
        }
        if(rightResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected sort Bool but was " + rightResult.sort.name + " in " + imp.toString)
        }
        TypeCheckResult(
            sanitizedTerm = Implication(leftResult.sanitizedTerm, rightResult.sanitizedTerm), 
            sort = BoolSort,
            containsConnectives = true, 
            containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers,
            containsItes = leftResult.containsItes || rightResult.containsItes,
            containsExists = leftResult.containsExists || rightResult.containsExists,
        )
    }
    
    override def visitIff(iff: Iff): TypeCheckResult = {
        val leftResult = visit(iff.left)
        val rightResult = visit(iff.right)
        
        if(leftResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected sort Bool but was " + leftResult.sort.name + " in " + iff.toString)
        }
        if(rightResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected sort Bool but was " + rightResult.sort.name + " in " + iff.toString)
        }
        TypeCheckResult(
            sanitizedTerm = Iff(leftResult.sanitizedTerm, rightResult.sanitizedTerm), 
            sort = BoolSort,
            containsConnectives = true, 
            containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers,
            containsItes = leftResult.containsItes || rightResult.containsItes,
            containsExists = leftResult.containsExists || rightResult.containsExists,
        )
    }
    
    override def visitEq(eq: Eq): TypeCheckResult = {
        val leftResult = visit(eq.left)
        val rightResult = visit(eq.right)
        
        if(leftResult.sort != rightResult.sort) {
            throw new TypeCheckException.WrongSort("Mismatched argument sorts " + leftResult.sort.toString + " and "
                + rightResult.sort.toString + " in " + eq.toString)
        }
        
        // Replaces (Bool) = (Bool) with Iff
        val sanTerm =
            if (leftResult.sort == BoolSort) Iff(leftResult.sanitizedTerm, rightResult.sanitizedTerm)
            else Eq(leftResult.sanitizedTerm, rightResult.sanitizedTerm)
        
        TypeCheckResult(
            sanitizedTerm = sanTerm, 
            sort = BoolSort,
            containsConnectives = true, 
            containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers,
            containsItes = leftResult.containsItes || rightResult.containsItes,
            containsExists = leftResult.containsExists || rightResult.containsExists,
        )
    }
    
    override def visitIfThenElse(ite: IfThenElse): TypeCheckResult = {
        val condResult = visit(ite.condition)
        val tResult = visit(ite.ifTrue)
        val fResult = visit(ite.ifFalse)
        
        if(condResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected sort Bool for ite condition but was  " + condResult.sort.name + " in " + ite.toString)
        }
        
        if(tResult.sort != fResult.sort) {
            throw new TypeCheckException.WrongSort("Mismatched argument sorts " + tResult.sort.toString + " and "
                + fResult.sort.toString + " in " + ite.toString)
        }
        
        // Replace if p then (Bool q) else (Bool r)
        // with (p and q) or ( (not p) and r) which is equivalent
        val sanTerm =
            if(tResult.sort == BoolSort) (
                (condResult.sanitizedTerm and tResult.sanitizedTerm) or (Not(condResult.sanitizedTerm) and fResult.sanitizedTerm))
            else IfThenElse(condResult.sanitizedTerm, tResult.sanitizedTerm, fResult.sanitizedTerm)
        
        TypeCheckResult(
            sanitizedTerm = sanTerm,
            sort = tResult.sort,
            containsConnectives = condResult.containsConnectives || tResult.containsConnectives || fResult.containsConnectives,
            containsQuantifiers = condResult.containsQuantifiers || tResult.containsQuantifiers || fResult.containsQuantifiers,
            containsItes = true,
            containsExists = condResult.containsExists || tResult.containsExists || fResult.containsExists
        )
    }
    
    override def visitApp(app: App): TypeCheckResult = {
        // Check argument:
        // 1. types match function declaration
        // 2. arguments contain no connectives or quantifiers
        val funcName = app.functionName

        if(! ( (signature hasFuncDeclWithName funcName) || (signature hasFuncDefWithName funcName) ) ) {
            throw new TypeCheckException.UnknownFunction("Could not find function: " + funcName)
        }
        
        // The typecheck results for each of the arguments
        val results = app.arguments.map(visit)

        // Note this is not strictly unacceptable, and we might actually fully support this outside of throwing this error
        /*
        if(results exists (_.containsQuantifiers)) {
            throw new TypeCheckException.BadStructure("Argument of " + funcName + " contains quantifier")
        }
        */

        // Sorts of the arguments
        val argSorts = results.map(_.sort)
        

        val resultSort: Sort = signature.queryFunction(funcName, argSorts) match {
            case None => throw new TypeCheckException.WrongSort(funcName + " cannot accept argument sorts " + argSorts.toString + " in " + app.toString)
            case Some(Left(fdecl)) => fdecl.resultSort
            case Some(Right(fdefn)) => fdefn.resultSort
        }
        
        TypeCheckResult(
            sanitizedTerm = App(funcName, results map (_.sanitizedTerm)),
            sort = resultSort,
            containsConnectives = results exists (_.containsConnectives),
            containsQuantifiers = false,
            containsItes = results exists (_.containsItes),
            containsExists = results exists (_.containsExists)
        )
    }
    
    override def visitBuiltinApp(bapp: BuiltinApp): TypeCheckResult = {
        val results = bapp.arguments.map(visit)
        val argSorts = results.map(_.sort)
        
        /* This seems to be unnessecary and was restricting what we can support. Leaving it in comments just in case.
        if(results.exists(_.containsConnectives)) {
            throw new TypeCheckException.BadStructure("Argument of " + bapp.function.toString + " contains connective")
        }
        if(results.exists(_.containsQuantifiers)) {
            throw new TypeCheckException.BadStructure("Argument of " + bapp.function.toString + " contains quantifier")
        }
        */
        bapp.function.resultSortFromArgSorts(argSorts) match {
            case Some(resultSort) => TypeCheckResult(
                sanitizedTerm = BuiltinApp(bapp.function, results.map(_.sanitizedTerm)), sort = resultSort,
                containsConnectives = false, 
                containsQuantifiers = false,
                containsItes = results exists (_.containsItes),
                containsExists = results exists (_.containsExists)
            )
            case None => throw new TypeCheckException.WrongSort("Builtin function " + bapp.function.toString + " cannot accept arguments of sorts " + argSorts.toString)
        }
    }


    override def visitClosure(c: Closure): TypeCheckResult = {
        // Check argument:
        // 1. types match function declaration
        // 2. arguments contain no connectives or quantifiers
        val funcName = c.functionName

        // Check function we are closing over exists
        if(! (signature hasFuncWithName  funcName) ) {
            throw new TypeCheckException.UnknownFunction("Could not find function: " + funcName)
        }
        
        val results = c.allArguments.map(visit)
        /*
        if (results.exists(_.containsConnectives)) {
            throw new TypeCheckException.BadStructure("Argument of ^" + c.functionName + " contains connective")
        }
        if (results.exists(_.containsQuantifiers)) {
            throw new TypeCheckException.BadStructure("Argument of ^" + c.functionName + " contains quantifier")
        }

        if (results.exists(_.containsItes)) {
            throw new TypeCheckException.BadStructure("Argument of ^" + c.functionName + " contains ites")
        }  
        */      
        // We assume closing over first 2 arguments
        if (results(0).sort != results(1).sort) {
            throw new TypeCheckException.WrongSort("Trying to close over arguments of different sorts in " + c.toString())
        }
        
        // This is the arguments to the closure. Will always be at least length 2 by construction
        val argSorts = results.map(_.sort)
        Errors.Internal.precondition(argSorts.length >= 2, c.toString() + "has only" + argSorts.length + " arguments! 2 or more expected")        // the sort we are closing over
        // The sort we are closing over
        val closingSort = argSorts(0)

        // Get sorts of the function/relation being closed over
        val (paramSorts, resultSort) = signature.queryFunction(funcName) match {
            case None => throw new TypeCheckException.UnknownFunction("Function " + funcName + " does not exist in signature when closing over it!")
            case Some(Left(FuncDecl(_, sorts, resultSort))) => (sorts.toList, resultSort)
            case Some(Right(FunctionDefinition(_, params, resultSort, _))) => (params.map(_.sort).toList, resultSort)
        }

        if (argSorts.length == 2) {
            // relation must be A->A or AxA-> Bool
            if (!((paramSorts.equals(List(closingSort)) && resultSort == closingSort) ||(paramSorts.equals(List(closingSort, closingSort)) && resultSort == BoolSort))){
                throw new TypeCheckException.WrongSort("Trying to close over " + funcName +" as unary function or binary relation in " + c.toString())
            }
        } else {
            // Check that arguments match the function declaration
            if (!(paramSorts == argSorts && resultSort == BoolSort)) {
                throw new TypeCheckException.WrongSort("Attempting to close over a relation that does not end in a BoolSort or with the wrong argument sorts in " + c.toString())
            }
        }

        TypeCheckResult(
            // sanitizedTerm = Closure(funcName, results map (_.sanitizedTerm), c.arg1, c.arg2),
            // Which cleaning works here?
            sanitizedTerm = c,
            sort = BoolSort, 
            containsConnectives = results exists (_.containsConnectives), 
            containsQuantifiers = results exists (_.containsQuantifiers),
            containsItes = results exists (_.containsItes),
            containsExists = results exists (_.containsExists) 
        )
    }

    override def visitReflexiveClosure(rc: ReflexiveClosure): TypeCheckResult = {
        // Check argument:
        // 1. types match function declaration
        // 2. arguments contain no connectives or quantifiers
        val funcName = rc.functionName

        if(! (signature hasFuncWithName  funcName) ) {
            throw new TypeCheckException.UnknownFunction("Could not find function: " + funcName)
        }
        
        val results = rc.allArguments.map(visit)
        /*
        if (results.exists(_.containsConnectives)) {
            throw new TypeCheckException.BadStructure("Argument of *" + rc.functionName + " contains connective")
        }
        if (results.exists(_.containsQuantifiers)) {
            throw new TypeCheckException.BadStructure("Argument of *" + rc.functionName + " contains quantifier")
        }
        if (results.exists(_.containsItes)) {
            throw new TypeCheckException.BadStructure("Argument of *" + rc.functionName + " contains ites")
        }
        */ 
        // We assunme closing over first 2 arguments
        if (results(0).sort != results(1).sort) {
            throw new TypeCheckException.WrongSort("Trying to close over arguments of different sorts in " + rc.toString())
        }
        
        // This is the arguments to the closure. Will always be at least length 2 by construction
        val argSorts = results.map(_.sort)
        Errors.Internal.precondition(argSorts.length >= 2, rc.toString() + "has only" + argSorts.length + " arguments! 2 or more expected")        // the sort we are closing over
        // The sort we are closing over
        val closingSort = argSorts(0)

        // Get sorts of the function/relation being closed over
        val (paramSorts, resultSort) = signature.queryFunction(funcName) match {
            case None => throw new TypeCheckException.UnknownFunction("Function " + funcName + " does not exist in signature when closing over it!")
            case Some(Left(FuncDecl(_, sorts, resultSort))) => (sorts.toList, resultSort)
            case Some(Right(FunctionDefinition(_, params, resultSort, _))) => (params.map(_.sort).toList, resultSort)
        }

        if (argSorts.length == 2) {
            // relation must be A->A or AxA-> Bool
            if (!((paramSorts.equals(List(closingSort)) && resultSort == closingSort) ||(paramSorts.equals(List(closingSort, closingSort)) && resultSort == BoolSort))){
                throw new TypeCheckException.WrongSort("Trying to close over " + funcName +" as unary function or binary relation in " + rc.toString())
            }
        } else {
            // Check that arguments match the function declaration
            if (!(paramSorts == argSorts && resultSort == BoolSort)) {
                throw new TypeCheckException.WrongSort("Attempting to close over a relation that does not end in a BoolSort or with the wrong argument sorts in " + rc.toString())
            }
        }

        TypeCheckResult(
            sanitizedTerm = rc,
            sort = BoolSort, 
            containsConnectives = results exists (_.containsConnectives), 
            containsQuantifiers = results exists (_.containsQuantifiers),
            containsItes = results exists (_.containsItes),
            containsExists = results exists (_.containsExists) 
        )
    }
    
    def visitDefnBody(t: Term): TypeCheckResult = {
        return visit(t)
    }
    override def visitExistsInner(exists: Exists): TypeCheckResult = {
        // Check variables don't clash with function names
        // and that their sort exists
        for(av <- exists.vars) {
            if(signature hasFuncDeclWithName  av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }

            if(signature hasFuncDefWithName  av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }

            if(!av.sort.isBuiltin && !(signature hasSort av.sort) ) {
                throw new TypeCheckException.UndeclaredSort("Undeclared sort " + av.sort.name + " in " + exists.toString)
            }
        }
        val bodyResult = visit(exists.body)
        if(bodyResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected Bool but was " + bodyResult.sort.name + " in " + exists.toString)
        }
        TypeCheckResult(
            sanitizedTerm = Exists(exists.vars, bodyResult.sanitizedTerm), 
            sort = BoolSort,
            containsConnectives = bodyResult.containsConnectives, 
            containsQuantifiers = true,
            containsItes = bodyResult.containsItes,
            containsExists = true,
        )
    }
    
    override def visitForallInner(forall: Forall): TypeCheckResult = {
        // Check variables don't clash with function names
        // and that their sort exists
        for(av <- forall.vars) {
            if(signature hasFuncDeclWithName  av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }

            if(signature hasFuncDefWithName   av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }

            if(!av.sort.isBuiltin && !(signature hasSort av.sort) ) {
                throw new TypeCheckException.UndeclaredSort("Undeclared sort " + av.sort.name + " in " + forall.toString)
            }
        }
        val bodyResult = visit(forall.body)
        if(bodyResult.sort != BoolSort) {
            throw new TypeCheckException.WrongSort("Expected Bool but was " + bodyResult.sort.name + " in " + forall.toString)
        }
        TypeCheckResult(
            sanitizedTerm = Forall(forall.vars, bodyResult.sanitizedTerm), 
            sort = BoolSort,
            containsConnectives = bodyResult.containsConnectives, 
            containsQuantifiers = true,
            containsItes = bodyResult.containsItes,
            containsExists = bodyResult.containsExists
        )
    }
    
    override def visitDomainElement(d: DomainElement): TypeCheckResult = {
        if( d.sort.isBuiltin ) {
            throw new TypeCheckException.WrongSort("Cannot make domain element of sort " + d.sort)
        }
        if(! (signature hasSort d.sort)) {
            throw new TypeCheckException.UndeclaredSort("Undeclared sort " + d.sort.name + " in " + d.toString)
        }
        TypeCheckResult(
            sanitizedTerm = d, 
            sort = d.sort, 
            containsConnectives = false, 
            containsQuantifiers = false,
            containsItes = false,
            containsExists = false,
        )
    }
    
    override def visitIntegerLiteral(literal: IntegerLiteral): TypeCheckResult =
       TypeCheckResult(
            sanitizedTerm = literal, 
            sort = IntSort,
            containsConnectives = false, 
            containsQuantifiers = false,
            containsItes = false,
            containsExists = false,
        )
    
    override def visitBitVectorLiteral(literal: BitVectorLiteral): TypeCheckResult =
       TypeCheckResult(
            sanitizedTerm = literal, 
            sort = BitVectorSort(literal.bitwidth),
            containsConnectives = false, 
            containsQuantifiers = false,
            containsItes = false,
            containsExists = false,
        )
    
    override def visitEnumValue(e: EnumValue): TypeCheckResult = signature.queryEnum(e) match {
        case Some(eSort: Sort) => 
            TypeCheckResult(
                sanitizedTerm = e, 
                sort = eSort, 
                containsConnectives = false, 
                containsQuantifiers = false,
                containsItes = false,
                containsExists = false,
            )
        case None => throw new TypeCheckException.UndeterminedSort("Could not determine sort of enum " + e.name)
    }
    
}