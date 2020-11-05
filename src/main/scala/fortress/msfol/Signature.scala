package fortress.msfol 

import fortress.data.InsertionOrderedSet
import fortress.util.Errors
import fortress.operations.TypeCheckResult
import scala.jdk.CollectionConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java

// Persistent and Immutable
// Internally consistent
// The constructor is private -- the only way to make signatures outside of this class
// is through the empty and withXYZ methods 
case class Signature private (
    sorts: Set[Sort],
    functionDeclarations: Set[FuncDecl],
    constants: Set[AnnotatedVar],
    enumConstants: Map[Sort, Seq[EnumValue]]
) extends TypeCheckQuerying {
    
    // TODO need to check this type is not builtin
    def withSort(t: Sort): Signature = {
        if(t.isBuiltin) this
        else {
            assertSortConsistent(t)
            Signature(sorts + t, functionDeclarations, constants, enumConstants)
        }
    }
    
    def withSorts(sorts: java.lang.Iterable[Sort]): Signature = {
        var sig: Signature = this
        sorts.forEach { t =>
            sig = sig.withSort(t)
        }
        sig
    }
    
    @varargs
    def withSorts(sorts: Sort*): Signature = withSorts(sorts.asJava)
    
    def withFunctionDeclaration(fdecl: FuncDecl): Signature = {
        assertFuncDeclConsistent(fdecl)
        Signature(sorts, functionDeclarations + fdecl, constants, enumConstants)
    }
    
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Signature = {
        var sig: Signature = this
        fdecls.forEach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        sig
    }
    
    def withFunctionDeclarations(fdecls: Iterable[FuncDecl]): Signature = {
        var sig = this
        fdecls.foreach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        sig
    }
    
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Signature = withFunctionDeclarations(fdecls.asJava)
    
    def withConstant(c: AnnotatedVar): Signature = {
        assertConstConsistent(c);
        Signature(sorts, functionDeclarations, constants + c, enumConstants)
    }
    
    def withConstants(constants: java.lang.Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.forEach { c =>
            sig = sig.withConstant(c)
        }
        sig
    }
    
    def withConstants(constants: Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.foreach { c =>
            sig = sig.withConstant(c)
        }
        sig;
    }
    
    @varargs
    def withConstants(constants: AnnotatedVar*): Signature = withConstants(constants.asJava)
    
    def withEnumSort(t: Sort, values: Seq[EnumValue]) = {
        // TODO more consistency checking
        Signature(sorts + t, functionDeclarations, constants, enumConstants + (t -> values))
    }
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO more consistency checking
        Signature(sorts + t, functionDeclarations, constants, enumConstants + (t -> values.asScala.toList))
    }
    
    // TypeChecking
    
    override def queryConstant(v: Var): Option[AnnotatedVar] = constants.find(_.variable == v)
    
    override def queryEnum(e: EnumValue): Option[Sort] = enumConstants.find {
        case (sort, enumConstants) => enumConstants contains e
    }.map { case (sort, _) => sort }
    
    override def queryFunction(name: String, argSorts: Seq[Sort]): Option[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.name == name && fdecl.argSorts == argSorts)
    
    override def queryUninterpretedFunction(name: String): Option[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.name == name)
    
    override def hasSort(sort: Sort): Boolean = sorts contains sort
    
    override def hasSortWithName(name: String): Boolean = sorts.exists(_.name == name)
    
    override def hasFunctionWithName(name: String): Boolean = functionDeclarations.exists(_.name == name)
    
    override def functionWithName(name: String): Option[FuncDecl] = functionDeclarations.find(_.name == name)
    
    def replaceIntegersWithBitVectors(bitwidth: Int): Signature = {
        def replaceSort(s: Sort): Sort = s match {
            case IntSort => BitVectorSort(bitwidth)
            case _ => s
        }
        
        val newSorts = sorts
        val newFunctionDeclarations = functionDeclarations.map(
            fdecl => FuncDecl(fdecl.name, fdecl.argSorts map replaceSort, replaceSort(fdecl.resultSort))
        )
        val newConstants = constants.map(c => c.variable of replaceSort(c.sort))
        val newEnums = enumConstants
        Signature(newSorts, newFunctionDeclarations, newConstants, newEnums)
    }
    
    def withoutEnums = Signature(sorts, functionDeclarations, constants, Map.empty)
    
    private
    def assertSortConsistent(t: Sort): Unit = {
        // Sort must not share a name with any function
        Errors.Internal.precondition(! hasFunctionWithName(t.name), "Name " + t.name + " shared by sort and function")
        
        // Sort must not share a name with any constant
        Errors.Internal.precondition(queryConstant(Var(t.name)).isEmpty, "Name " + t.name + " shared by sort and constant")
    }
    
    private 
    def assertConstConsistent(c: AnnotatedVar): Unit = {
        // Constant's sort must be within the set of sorts
        Errors.Internal.precondition(c.sort.isBuiltin || hasSort(c.sort), "Constant " + c.toString + " of undeclared sort ")
        
        // Constant cannot share a name with a constant of a different sort
        Errors.Internal.precondition(queryConstant(c.variable).filter(_.sort != c.sort).isEmpty, "Constant " + c.name + " declared with two different sorts")
        
        // Constant cannot share a name with any function 
        Errors.Internal.precondition(! hasFunctionWithName(c.name), "Name " + c.name + " shared by constant and function")
    }
    
    private
    def assertFuncDeclConsistent(fdecl: FuncDecl): Unit = {
        // Argument sorts must exist in sort set
        Errors.Internal.precondition(fdecl.argSorts.forall(s => s.isBuiltin || hasSort(s)),
            "Function " + fdecl.name + " has argument sorts that are undeclared")
            
        // Result sort must exist in sort set
        Errors.Internal.precondition(fdecl.resultSort.isBuiltin || hasSort(fdecl.resultSort),
            "Function " + fdecl.name + " has result sort that is undeclared")
            
        // Function must not share name with a constant
        Errors.Internal.precondition(queryConstant(Var(fdecl.name)).isEmpty,
            "Name " + fdecl.name +  " shared by function and constant")
        
        // Function must not share name with a sort
        Errors.Internal.precondition(! hasSortWithName(fdecl.name), "Name " + fdecl.name +  " shared by function and sort")
        
        // Function must not share name with another function, unless it is the same function
        Errors.Internal.precondition(
            ! hasFunctionWithName(fdecl.name) || // No function has same name
            queryFunction(fdecl.name, fdecl.argSorts).filter(_ == fdecl).nonEmpty, // Same function exists
            "Function " + fdecl.name + " declared with two different sorts")
    }
    
    override def toString: String = {
        val sortString = "Sorts: " + sorts.mkString(", ")
        
        val enumString = "Enum Sorts:\n" + enumConstants.map {
            case(sort, enumValues) => sort.name + " = {" + enumValues.mkString(", ") + "}"
        }.mkString("\n")
        
        val funcString = "Function declarations:\n" + functionDeclarations.mkString("\n")
        val constString = "Constants:\n" + constants.mkString("\n")
        
        // Slow but doesn't matter
        var result = "Signature"
        if(sorts.nonEmpty) { result += "\n" + sortString }
        if(enumConstants.nonEmpty) { result += "\n" + enumString }
        if(functionDeclarations.nonEmpty) { result += "\n" + funcString }
        if(constants.nonEmpty) { result += "\n" + constString }
        result
    }
}

object Signature {
    def empty: Signature = 
        // For testing consistency for symmetry breaking, use an insertion ordered set
        Signature(InsertionOrderedSet.empty[Sort], InsertionOrderedSet.empty, InsertionOrderedSet.empty, Map.empty)
}
