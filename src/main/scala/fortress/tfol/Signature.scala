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
    sorts: Set[Sort],
    functionDeclarations: Set[FuncDecl],
    constants: Set[AnnotatedVar],
    enumConstants: Map[Sort, Seq[EnumValue]],
    extensions: Set[SignatureExtension]
) extends ExtensibleTypeChecking {
    
    // TODO need to check this type is not builtin
    def withSort(t: Sort): Signature = {
        assertSortConsistent(t)
        Signature(sorts + t, functionDeclarations, constants, enumConstants, extensions)
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
        Signature(sorts, functionDeclarations + fdecl, constants, enumConstants, extensions)
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
        Signature(sorts, functionDeclarations, constants + c, enumConstants, extensions)
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
        Signature(sorts + t, functionDeclarations, constants, enumConstants + (t -> values), extensions)
    }
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO more consistency checking
        Signature(sorts + t, functionDeclarations, constants, enumConstants + (t -> values.asScala.toList), extensions)
    }
    
    // TypeChecking
    
    override def queryConstantBase(v: Var): Option[AnnotatedVar] = constants.find(_.variable == v)
    
    override def queryEnumBase(e: EnumValue): Option[Sort] = enumConstants.find {
        case (sort, enumConstants) => enumConstants contains e
    }.map { case (sort, _) => sort }
    
    override def queryFunctionBase(name: String, argSorts: Seq[Sort]): Option[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.name == name && fdecl.argSorts == argSorts)
    
    override def queryUninterpretedFunctionBase(name: String): Option[FuncDecl] = functionDeclarations.find(_.name == name)
    
    override def hasSortBase(sort: Sort): Boolean = extensions.exists(_.hasSort(sort)) || (sorts contains sort)
    
    override def hasSortWithNameBase(name: String): Boolean = extensions.exists(_.hasSortWithName(name)) || sorts.exists(_.name == name)
    
    override def hasFunctionWithNameBase(name: String): Boolean = (extensions.exists(_.hasFunctionWithName(name))) || functionDeclarations.exists(_.name == name)
    
    private[tfol]
    def getConstants: java.util.Set[AnnotatedVar] = constants.asJava
    
    private[tfol]
    def getFunctionDeclarations: java.util.Set[FuncDecl] = functionDeclarations.asJava
    
    private[tfol]
    def getSorts: java.util.Set[Sort] = sorts.asJava
    
    def withIntegers: Signature = Signature(sorts, functionDeclarations, constants, enumConstants, extensions + IntegerExtension)
    
    def withoutEnums = Signature(sorts, functionDeclarations, constants, Map.empty, extensions)
    
    private
    def assertSortConsistent(t: Sort): Unit = {
        // Sort must not share a name with any function
        Errors.precondition(! functionDeclarations.exists(
            (fdecl: FuncDecl) => fdecl.name == t.name
        ), "Name " + t.name + " shared by sort and function")
        
        // Sort must not share a name with any constant
        Errors.precondition(! constants.exists(
            (c: AnnotatedVar) => c.name == t.name
        ), "Name " + t.name + " shared by sort and constant")
    }
    
    private 
    def assertConstConsistent(c: AnnotatedVar): Unit = {
        // Constant's sort must be within the set of sorts
        Errors.precondition(sorts contains c.sort,
            "Constant " + c.toString + " of undeclared sort ")
        
        // Constant's cannot share a name with a constant of a different sorts
        Errors.precondition(! constants.exists(
            (otherConst: AnnotatedVar) => otherConst.name == c.name && otherConst != c
        ), "Constant " + c.name + " declared with two different sorts")
        
        // Constant cannot share a name with any function 
        Errors.precondition(! functionDeclarations.exists(
            (fdecl: FuncDecl) => fdecl.name == c.name
        ), "Name " + c.name + " shared by constant and function")
    }
    
    private
    def assertFuncDeclConsistent(fdecl: FuncDecl): Unit = {
        // Argument sorts must exist in sort set
        Errors.precondition(fdecl.argSorts.forall(t => sorts contains t),
            "Function " + fdecl.name + " has argument sorts that are undeclared")
            
        // Result sort must exist in sort set
        Errors.precondition(sorts.contains(fdecl.resultSort),
            "Function " + fdecl.name + " has result sort that is undeclared")
            
        // Function must not share name with a constant
        Errors.precondition(! constants.exists(
            (c: AnnotatedVar) => c.name == fdecl.name
        ), "Name " + fdecl.name +  " shared by function and constant")
        
        // Function must not share name with a sort
        Errors.precondition(! sorts.exists(
            (t: Sort) => t.name == fdecl.name
        ), "Name " + fdecl.name +  " shared by function and sort")
        
        // Function must not share name with another function, unless it is the same function
        Errors.precondition(! functionDeclarations.exists(
            (otherFun: FuncDecl) => otherFun.name == fdecl.name && otherFun != fdecl
        ), "Function " + fdecl.name + " declared with two different sorts")
    }
    
    override def toString: String = "Signature <<\n" + sorts.mkString("\n") + "\n" + functionDeclarations.mkString("\n") + "\n" + constants.mkString("\n") +
        "\nExtensions:\n" + extensions.mkString("\n") + ">>"
}

object Signature {
    def empty: Signature = 
        // For testing consistency for symmetry breaking, use an insertion ordered set
        Signature(InsertionOrderedSet.empty[Sort] + BoolSort, InsertionOrderedSet.empty, InsertionOrderedSet.empty, Map(), Set())
}
