package fortress.tfol.operations

import scala.collection.immutable.Seq // Use immutable seq by default

import fortress.util.Errors
import fortress.tfol._
import fortress.data._

case class TypeCheckResult(
    sanitizedTerm: Term,
    sort: Type,
    containsConnectives: Boolean,
    containsQuantifiers: Boolean
)

/** Given a signature and a term, typechecks the term with respect to the signature.
 * Returns a TypeCheckResult containing the type of the term, AND a new term
 * that is equal to the old term but with instances of Eq replaced with Iff
 * when comparing Bool types. Such a term is called "sanitized". */
class TypeChecker(signature: Signature) extends TermVisitorWithTypeContext[TypeCheckResult](signature) {
    override def visitTop: TypeCheckResult =
        TypeCheckResult(sanitizedTerm = Top, sort = BoolType, containsConnectives = false, containsQuantifiers = false)
        
    override def visitBottom: TypeCheckResult =
        TypeCheckResult(sanitizedTerm = Bottom, sort = BoolType, containsConnectives = false, containsQuantifiers = false)
    
    override def visitVar(variable: Var): TypeCheckResult = {
        // Check variable is not an already declared function symbol
        // This must be done even with a consistent signature
        // TODO: this behaviour should be documented
        // TODO: is this considered poorly typed or a different kind of error?
        if(signature hasFunctionWithName variable.name) {
            throw new TypeCheckException.NameConflict("Variable or constant name " + variable.name + " conflicts with existing function symbol")
        }
        
        // Check variable is not an already declared type symbol
        if(signature hasTypeWithName variable.name) {
            throw new TypeCheckException.NameConflict("Variable or constant name " + variable.name + " conflicts with existing type symbol")
        }
        
        val typeMaybe = lookupType(variable)
        if(!typeMaybe.isPresent()) {
            throw new TypeCheckException.UndeterminedType("Could not determine type of variable " + variable.name)
        }
        
        TypeCheckResult(sanitizedTerm = variable, sort = typeMaybe.get,
            containsConnectives = false, containsQuantifiers = false)
    }
    
    override def visitNot(not: Not): TypeCheckResult = {
        val bodyResult = visit(not.body)
        if(bodyResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Argument of negation is of type " + bodyResult.sort.name + " in " + not.toString)
        }
        TypeCheckResult(sanitizedTerm = Not(bodyResult.sanitizedTerm), sort = BoolType,
            containsConnectives = true, containsQuantifiers = bodyResult.containsQuantifiers)
    }
    
    override def visitAndList(andList: AndList): TypeCheckResult = {
        val results = andList.arguments.map(visit)
        for(result <- results) {
            if(result.sort != BoolType) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + result.sort.name + " in " + andList.toString)
            }
        }
        TypeCheckResult(sanitizedTerm = AndList(results.map(_.sanitizedTerm)), sort = BoolType,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers))
    }
    
    override def visitOrList(orList: OrList): TypeCheckResult = {
        val results = orList.arguments.map(visit)
        for(result <- results) {
            if(result.sort != BoolType) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + result.sort.name + " in " + orList.toString)
            }
        }
        TypeCheckResult(sanitizedTerm = OrList(results.map(_.sanitizedTerm)), sort = BoolType,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers))
    }
    
    override def visitDistinct(distinct: Distinct): TypeCheckResult = {
        val results: Seq[TypeCheckResult] = distinct.arguments.map(visit)
        
        // Check sorts all the same
        val sorts: Seq[Type] = results.map(_.sort)
        if(sorts.distinct.size > 1) {
            throw new TypeCheckException.WrongArgType("Arguments of multiple types " + sorts.toString + " in " + distinct.toString)
        }
        
        TypeCheckResult(sanitizedTerm = Distinct(results.map(_.sanitizedTerm)), sort = BoolType,
            containsConnectives = true,
            containsQuantifiers = results.exists(_.containsQuantifiers))
    }
    
    override def visitImplication(imp: Implication): TypeCheckResult = {
        val leftResult = visit(imp.left)
        val rightResult = visit(imp.right)
        
        if(leftResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected type Bool but was " + leftResult.sort.name + " in " + imp.toString)
        }
        if(rightResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected type Bool but was " + rightResult.sort.name + " in " + imp.toString)
        }
        TypeCheckResult(sanitizedTerm = Implication(leftResult.sanitizedTerm, rightResult.sanitizedTerm), sort = BoolType,
            containsConnectives = true, containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers)
    }
    
    override def visitIff(iff: Iff): TypeCheckResult = {
        val leftResult = visit(iff.left)
        val rightResult = visit(iff.right)
        
        if(leftResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected type Bool but was " + leftResult.sort.name + " in " + iff.toString)
        }
        if(rightResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected type Bool but was " + rightResult.sort.name + " in " + iff.toString)
        }
        TypeCheckResult(sanitizedTerm = Iff(leftResult.sanitizedTerm, rightResult.sanitizedTerm), sort = BoolType,
            containsConnectives = true, containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers)
    }
    
    override def visitEq(eq: Eq): TypeCheckResult = {
        val leftResult = visit(eq.left)
        val rightResult = visit(eq.right)
        
        if(leftResult.sort != rightResult.sort) {
            throw new TypeCheckException.WrongArgType("Mismatched argument types " + leftResult.sort.toString + " and "
                + rightResult.sort.toString + " in " + eq.toString)
        }
        
        // Replaces (Bool) = (Bool) with Iff
        val sanTerm =
            if (leftResult.sort == BoolType) Iff(leftResult.sanitizedTerm, rightResult.sanitizedTerm)
            else Eq(leftResult.sanitizedTerm, rightResult.sanitizedTerm)
        
        TypeCheckResult(sanitizedTerm = sanTerm, sort = BoolType,
            containsConnectives = true, containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers)
    }
    
    override def visitApp(app: App): TypeCheckResult = {
        // Check argument:
        // 1. types match function declaration
        // 2. arguments contain no connectives or quantifiers
        val funcName = app.functionName
        
        if(! (signature hasFunctionWithName funcName) ) {
            throw new TypeCheckException.UnknownFunction("Could not find function " + funcName)
        }
        
        val results = app.arguments.map(visit)
        val argSorts = results.map(_.sort)
        val fdecl = signature.queryFunction(funcName, argSorts) match {
            case None => throw throw new TypeCheckException.WrongArgType(funcName + " cannot accept argument types " + argSorts.toString + " in " + app.toString)
            case Some(fdecl) => fdecl
        }
        
        if(results.exists(_.containsConnectives)) {
            throw new TypeCheckException.BadStructure("Argument of " + funcName + " contains connective")
        }
        if(results.exists(_.containsQuantifiers)) {
            throw new TypeCheckException.BadStructure("Argument of " + funcName + " contains quantifier")
        }
        
        TypeCheckResult(sanitizedTerm = App(funcName, results.map(_.sanitizedTerm)), sort = fdecl.resultType,
            containsConnectives = false, containsQuantifiers = false)
    }
    
    override def visitExistsInner(exists: Exists): TypeCheckResult = {
        // Check variables don't clash with function names
        // and that their type exists
        for(av <- exists.vars) {
            if(signature hasFunctionWithName av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }
            if(! (signature hasType av.sort) ) {
                throw new TypeCheckException.UnknownType("Unknown type " + av.sort.name + " in " + exists.toString)
            }
        }
        val bodyResult = visit(exists.body)
        if(bodyResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected Bool but was " + bodyResult.sort.name + " in " + exists.toString)
        }
        TypeCheckResult(sanitizedTerm = Exists(exists.vars, bodyResult.sanitizedTerm), sort = BoolType,
            containsConnectives = bodyResult.containsConnectives, containsQuantifiers = true)
    }
    
    override def visitForallInner(forall: Forall): TypeCheckResult = {
        // Check variables don't clash with function names
        // and that their type exists
        for(av <- forall.vars) {
            if(signature hasFunctionWithName av.name) {
                throw new TypeCheckException.NameConflict("Variable name " + av.name + " conflicts with existing function symbol")
            }
            if(! (signature hasType av.sort) ) {
                throw new TypeCheckException.UnknownType("Unknown type " + av.sort.name + " in " + forall.toString)
            }
        }
        val bodyResult = visit(forall.body)
        if(bodyResult.sort != BoolType) {
            throw new TypeCheckException.WrongArgType("Expected Bool but was " + bodyResult.sort.name + " in " + forall.toString)
        }
        TypeCheckResult(sanitizedTerm = Forall(forall.vars, bodyResult.sanitizedTerm), sort = BoolType,
            containsConnectives = bodyResult.containsConnectives, containsQuantifiers = true)
    }
    
    override def visitDomainElement(d: DomainElement): TypeCheckResult = {
        if(! (signature hasType d.sort)) {
            throw new TypeCheckException.UnknownType("Unkown type " + d.sort.name + " in " + d.toString)
        }
        TypeCheckResult(sanitizedTerm = d, sort = d.sort, containsConnectives = false, containsQuantifiers = false)
    }
    
    override def visitIntegerLiteral(literal: IntegerLiteral): TypeCheckResult = {
        // Should fail if Int is not in signature
        if(! (signature hasType IntType) ) {
            throw new TypeCheckException.UnknownType("Given signature does not include integers")
        } else {
           TypeCheckResult(sanitizedTerm = literal, sort = IntType,
                containsConnectives = false, containsQuantifiers = false)
        }
    }
    
    override def visitBitVectorLiteral(literal: BitVectorLiteral): TypeCheckResult = {
        // Should fail if BitVector is not in signature
        if(! (signature hasType BitVectorType(literal.bitWidth)) ) {
            throw new TypeCheckException.UnknownType("Given signature does not include bit vectors")
        } else {
           TypeCheckResult(sanitizedTerm = literal, sort = BitVectorType(literal.bitWidth),
                containsConnectives = false, containsQuantifiers = false)
        }
    }
    
    override def visitEnumValue(e: EnumValue) = signature.queryEnum(e) match {
        case Some(eSort: Type) => TypeCheckResult(sanitizedTerm = e, sort = eSort, containsConnectives = false, containsQuantifiers = true)
        case None => throw new TypeCheckException.UndeterminedType("Could not determine type of enum " + e.name)
    }
    
}
