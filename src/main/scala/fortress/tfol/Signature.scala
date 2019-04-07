package fortress.tfol 

import fortress.data.InsertionOrderedSet
import fortress.util.Errors
import fortress.tfol.operations.TypeCheckResult
import scala.collection.JavaConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java

// Persistent and Immutable
// Internally consistent
// The constructor is private -- the only way to make signatures outside of this class
// is through the empty and withXYZ methods 
case class Signature private (
    types: Set[Type],
    functionDeclarations: Set[FuncDecl],
    constants: Set[AnnotatedVar]
) {
    
    def withType(t: Type): Signature = {
        assertTypeConsistent(t)
        Signature(types + t, functionDeclarations, constants)
    }
    
    def withTypes(types: java.lang.Iterable[Type]): Signature = {
        var sig: Signature = this
        types.forEach { t =>
            sig = sig.withType(t)
        }
        sig
    }
    
    @varargs
    def withTypes(types: Type*): Signature = withTypes(types.asJava)
    
    def withFunctionDeclaration(fdecl: FuncDecl): Signature = {
        assertFuncDeclConsistent(fdecl)
        Signature(types, functionDeclarations + fdecl, constants)
    }
    
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Signature = {
        var sig: Signature = this;
        fdecls.forEach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        return sig
    }
    
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Signature = withFunctionDeclarations(fdecls.asJava)
    
    def withConstant(c: AnnotatedVar): Signature = {
        assertConstConsistent(c);
        Signature(types, functionDeclarations, constants + c);
    }
    
    def withConstants(constants: java.lang.Iterable[AnnotatedVar]): Signature = {
        var sig = this;
        constants.forEach { c =>
            sig = sig.withConstant(c);
        }
        return sig;
    }
    
    @varargs
    def withConstants(constants: AnnotatedVar*): Signature = withConstants(constants.asJava)
    
    def lookupConstant(v: Var): java.util.Optional[AnnotatedVar] =
        constants.find(c => c.getVar == v) match {
            case Some(av: AnnotatedVar) => java.util.Optional.of(av)
            case None => java.util.Optional.empty[AnnotatedVar]
        }
    
    def lookupFunctionDeclaration(functionName: String): java.util.Optional[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.getName == functionName) match {
            case Some(fdecl: FuncDecl) => java.util.Optional.of(fdecl)
            case None => java.util.Optional.empty[FuncDecl]
        }
    
    def hasType(name: String): Boolean = types.contains(Type.mkTypeConst(name))
    
    def hasType(sort: Type): Boolean = types.contains(sort)
    
    private[tfol]
    def getConstants: java.util.Set[AnnotatedVar] = constants.asJava
    
    private[tfol]
    def getFunctionDeclarations: java.util.Set[FuncDecl] = functionDeclarations.asJava
    
    private[tfol]
    def getTypes: java.util.Set[Type] = types.asJava
    
    private
    def assertTypeConsistent(t: Type): Unit = {
        // Type must not share a name with any function
        Errors.precondition(! functionDeclarations.exists(
            (fdecl: FuncDecl) => fdecl.getName == t.getName
        ), "Name " + t.getName + " shared by type and function")
        
        // Type must not share a name with any constant
        Errors.precondition(! constants.exists(
            (c: AnnotatedVar) => c.getName == t.getName
        ), "Name " + t.getName + " shared by type and constant")
    }
    
    private 
    def assertConstConsistent(c: AnnotatedVar): Unit = {
        // Constant's type must be within the set of types
        Errors.precondition(types.contains(c.getType),
            "Constant " + c.toString + " of undeclared type ")
        
        // Constant's cannot share a name with a constant of a different type
        Errors.precondition(! constants.exists(
            (otherConst: AnnotatedVar) => otherConst.getName == c.getName && otherConst != c
        ), "Constant " + c.getName + " declared with two different types")
        
        // Constant cannot share a name with any function 
        Errors.precondition(! functionDeclarations.exists(
            (fdecl: FuncDecl) => fdecl.getName == c.getName
        ), "Name " + c.getName + " shared by constant and function")
    }
    
    private
    def assertFuncDeclConsistent(fdecl: FuncDecl): Unit = {
        // Argument types must exist in type set
        Errors.precondition(fdecl.argTypes.forall(t => types.contains(t)),
            "Function " + fdecl.getName + " has argument types that are undeclared")
            
        // Result type must exist in type set
        Errors.precondition(types.contains(fdecl.getResultType),
            "Function " + fdecl.getName + " has result type that is undeclared")
            
        // Function must not share name with a constant
        Errors.precondition(! constants.exists(
            (c: AnnotatedVar) => c.getName == fdecl.getName
        ), "Name " + fdecl.getName +  " shared by function and constant")
        
        // Function must not share name with a type
        Errors.precondition(! types.exists(
            (t: Type) => t.getName == fdecl.getName
        ), "Name " + fdecl.getName +  " shared by function and type")
        
        // Function must not share name with another function, unless it is the same function
        Errors.precondition(! functionDeclarations.exists(
            (otherFun: FuncDecl) => otherFun.getName == fdecl.getName && otherFun != fdecl
        ), "Function " + fdecl.getName + " declared with two different types")
    }
}

object Signature {
    def empty: Signature = Signature(InsertionOrderedSet.empty[Type] + Type.Bool, InsertionOrderedSet.empty, InsertionOrderedSet.empty) // For testing consistency, use an insertion ordered set
}
