package fortress.tfol 

import fortress.data.InsertionOrderedSet
import fortress.util.Errors
import fortress.tfol.operations.TypeCheckResult
import scala.collection.JavaConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import scala.collection.immutable.Seq // Use immutable seq by default

// Persistent and Immutable
// Internally consistent
// The constructor is private -- the only way to make signatures outside of this class
// is through the empty and withXYZ methods 
case class Signature private (
    types: Set[Type],
    functionDeclarations: Set[FuncDecl],
    constants: Set[AnnotatedVar],
    enumConstants: Map[Type, Seq[EnumValue]],
    extensions: Set[SignatureExtension]
) extends TypeCheckQuerying {
    
    // TODO need to check this type is not builtin
    def withType(t: Type): Signature = {
        assertTypeConsistent(t)
        Signature(types + t, functionDeclarations, constants, enumConstants, extensions)
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
        Signature(types, functionDeclarations + fdecl, constants, enumConstants, extensions)
    }
    
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Signature = {
        var sig: Signature = this
        fdecls.forEach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        return sig
    }
    
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Signature = withFunctionDeclarations(fdecls.asJava)
    
    def withConstant(c: AnnotatedVar): Signature = {
        assertConstConsistent(c);
        Signature(types, functionDeclarations, constants + c, enumConstants, extensions)
    }
    
    def withConstants(constants: java.lang.Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.forEach { c =>
            sig = sig.withConstant(c)
        }
        return sig
    }
    
    def withConstants(constants: Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.foreach { c =>
            sig = sig.withConstant(c)
        }
        return sig;
    }
    
    @varargs
    def withConstants(constants: AnnotatedVar*): Signature = withConstants(constants.asJava)
    
    def withEnumType(t: Type, values: Seq[EnumValue]) = {
        // TODO more consistency checking
        Signature(types + t, functionDeclarations, constants, enumConstants + (t -> values), extensions)
    }
    
    def withEnumType(t: Type, values: java.util.List[EnumValue]) = {
        // TODO more consistency checking
        Signature(types + t, functionDeclarations, constants, enumConstants + (t -> values.asScala.toList), extensions)
    }
    
    def queryConstant(v: Var): Option[AnnotatedVar] = constants.find(_.variable == v)
    
    def queryEnum(v: Var): Option[AnnotatedVar] = enumConstants.find {
        case (sort, enumConstants) => enumConstants contains v
    }.map { case (sort, _) => v of sort }
    
    def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl] = {
        val matches: Set[FuncDecl] = extensions.flatMap(extension => extension.queryFunction(name, argTypes))
        Errors.assertion(matches.size <= 1, "Found multiple matches to function " + name + ": " + argTypes)
        if(matches.nonEmpty) Some(matches.head)
        else functionDeclarations.find(fdecl => fdecl.getName == name && fdecl.argTypes == argTypes)
    }
    
    def queryUninterpretedFunction(name: String): Option[FuncDecl] = functionDeclarations.find(_.name == name)
    
    def hasType(sort: Type): Boolean = extensions.exists(_.hasType(sort)) || (types contains sort)
    
    def hasTypeWithName(name: String): Boolean = extensions.exists(_.hasTypeWithName(name)) || types.exists(_.name == name)
    
    def hasFunctionWithName(name: String): Boolean = (extensions.exists(_.hasFunctionWithName(name))) || functionDeclarations.exists(_.name == name)
    
    private[tfol]
    def getConstants: java.util.Set[AnnotatedVar] = constants.asJava
    
    private[tfol]
    def getFunctionDeclarations: java.util.Set[FuncDecl] = functionDeclarations.asJava
    
    private[tfol]
    def getTypes: java.util.Set[Type] = types.asJava
    
    def withIntegers: Signature = Signature(types, functionDeclarations, constants, enumConstants, extensions + IntegerExtension)
    
    def withoutEnums = Signature(types, functionDeclarations, constants, Map.empty, extensions)
    
    private
    def assertTypeConsistent(t: Type): Unit = {
        // Type must not share a name with any function
        Errors.precondition(! functionDeclarations.exists(
            (fdecl: FuncDecl) => fdecl.getName == t.name
        ), "Name " + t.name + " shared by type and function")
        
        // Type must not share a name with any constant
        Errors.precondition(! constants.exists(
            (c: AnnotatedVar) => c.getName == t.name
        ), "Name " + t.name + " shared by type and constant")
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
            (t: Type) => t.name == fdecl.getName
        ), "Name " + fdecl.getName +  " shared by function and type")
        
        // Function must not share name with another function, unless it is the same function
        Errors.precondition(! functionDeclarations.exists(
            (otherFun: FuncDecl) => otherFun.getName == fdecl.getName && otherFun != fdecl
        ), "Function " + fdecl.getName + " declared with two different types")
    }
    
    override def toString: String = "Signature <<\n" + types.mkString("\n") + "\n" + functionDeclarations.mkString("\n") + "\n" + constants.mkString("\n") +
        "\nExtensions:\n" + extensions.mkString("\n") + ">>"
}

object Signature {
    def empty: Signature = 
        // For testing consistency for symmetry breaking, use an insertion ordered set
        Signature(InsertionOrderedSet.empty[Type] + Type.Bool, InsertionOrderedSet.empty, InsertionOrderedSet.empty, Map(), Set())
}
