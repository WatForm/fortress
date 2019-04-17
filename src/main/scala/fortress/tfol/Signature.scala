package fortress.tfol 

import fortress.data.InsertionOrderedSet
import fortress.util.Errors
import fortress.tfol.operations.TypeCheckResult
import scala.collection.JavaConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import scala.collection.immutable.Seq // Use immutable seq by default

trait SignatureTypechecking {
    def hasType(sort: Type): Boolean
    def hasTypeWithName(name: String): Boolean
    def hasFunctionWithName(name: String): Boolean
    def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl]
    def queryConstant(v: Var): Option[AnnotatedVar]
    
    def queryFunctionJava(name: String, argTypes: java.util.List[Type]): java.util.Optional[FuncDecl] =
        queryFunction(name, argTypes.asScala.toList) match {
            case Some(fdecl) => java.util.Optional.of[FuncDecl](fdecl)
            case None => java.util.Optional.empty[FuncDecl]()
        }
        
    def queryConstantJava(v: Var): java.util.Optional[AnnotatedVar] =
        queryConstant(v) match {
            case Some(av: AnnotatedVar) => java.util.Optional.of(av)
            case None => java.util.Optional.empty[AnnotatedVar]
        }
}

// Persistent and Immutable
// Internally consistent
// The constructor is private -- the only way to make signatures outside of this class
// is through the empty and withXYZ methods 
case class Signature private (
    types: Set[Type],
    functionDeclarations: Set[FuncDecl],
    constants: Set[AnnotatedVar],
    extensions: Set[SignatureExtension]
) extends SignatureTypechecking {
    
    // TODO need to check this type is not builtin
    def withType(t: Type): Signature = {
        assertTypeConsistent(t)
        Signature(types + t, functionDeclarations, constants, extensions)
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
        Signature(types, functionDeclarations + fdecl, constants, extensions)
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
        Signature(types, functionDeclarations, constants + c, extensions)
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
    
    def queryConstant(v: Var): Option[AnnotatedVar] = constants.find(_.variable == v)
    
    def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl] = {
        val matches: Set[FuncDecl] = extensions.flatMap(extension => extension.queryFunction(name, argTypes))
        Errors.assertion(matches.size <= 1, "Found multiple matches to function " + name + ": " + argTypes)
        if(matches.nonEmpty) Some(matches.head)
        else functionDeclarations.find(fdecl => fdecl.getName == name && fdecl.argTypes == argTypes)
    }
    
    def hasType(sort: Type): Boolean = extensions.exists(_.hasType(sort)) || (types contains sort)
    
    def hasTypeWithName(name: String): Boolean = extensions.exists(_.hasTypeWithName(name)) || types.exists(_.name == name)
    
    def hasFunctionWithName(name: String): Boolean = (extensions.exists(_.hasFunctionWithName(name))) || functionDeclarations.exists(_.name == name)
    
    private[tfol]
    def getConstants: java.util.Set[AnnotatedVar] = constants.asJava
    
    private[tfol]
    def getFunctionDeclarations: java.util.Set[FuncDecl] = functionDeclarations.asJava
    
    private[tfol]
    def getTypes: java.util.Set[Type] = types.asJava
    
    def withIntegers: Signature = new Signature(types, functionDeclarations, constants, extensions + IntegerExtension)
    
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
        Signature(InsertionOrderedSet.empty[Type] + Type.Bool, InsertionOrderedSet.empty, InsertionOrderedSet.empty, Set())
}


trait SignatureExtension extends SignatureTypechecking

// Cannot implement this as a mixin -- must implement as an object
object IntegerExtension extends SignatureExtension {
    val plus = "+"
    val minus = "-"
    val times = "*"
    val div = "div"
    val mod = "mod"
    val abs = "abs"
    val LE = "<="
    val LT = "<"
    val GE = ">="
    val GT = ">"
    
    override def hasType(sort: Type): Boolean = sort == IntType
    
    override def hasTypeWithName(name: String): Boolean = name == IntType.name
    
    override def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl] = (name, argTypes) match {
        case (`plus`, Seq(IntType, IntType)) => Some(FuncDecl(plus, IntType, IntType, IntType))
        case (`minus`, Seq(IntType, IntType)) => Some(FuncDecl(minus, IntType, IntType, IntType)) // Binary minus
        case (`minus`, Seq(IntType)) => Some(FuncDecl(minus, IntType, IntType)) // Unary minus
        case (`times`, Seq(IntType, IntType)) => Some(FuncDecl(times, IntType, IntType, IntType))
        case (`div`, Seq(IntType, IntType)) => Some(FuncDecl(div, IntType, IntType, IntType))
        case (`mod`, Seq(IntType, IntType)) => Some(FuncDecl(mod, IntType, IntType))
        case (`abs`, Seq(IntType)) => Some(FuncDecl(abs, IntType, IntType))
        case (`LE`, Seq(IntType, IntType)) => Some(FuncDecl(LE, IntType, IntType, BoolType))
        case (`LT`, Seq(IntType, IntType)) => Some(FuncDecl(LT, IntType, IntType, BoolType))
        case (`GE`, Seq(IntType, IntType)) => Some(FuncDecl(GE, IntType, IntType, BoolType))
        case (`GT`, Seq(IntType, IntType)) => Some(FuncDecl(GT, IntType, IntType, BoolType))
        case _ => None
    }
    
    override def hasFunctionWithName(name: String): Boolean = 
        Set(plus, minus, times, div, mod, abs, LE, LT, GE, GT) contains name
        
    override def queryConstant(v: Var): Option[AnnotatedVar] = None
    
    override def toString: String = "Integer Extension"
}

// TODO make this a mixin
object BitVectorSignature {
    def hasType(sort: Type) = sort match {
        case BitVectorType(_) => true
        case _ => false
    }
    
    def queryFunction(name: String, argTypes: Seq[Type]): Option[Type] = (name, argTypes) match {
        case (binop, Seq(BitVectorType(n), BitVectorType(m)))
            if (binaryOperations contains binop) && (n == m) => Some(BitVectorType(n))
        case (unop, Seq(BitVectorType(n))) if (unaryOperations contains unop) => Some(BitVectorType(n))
        case _ => None
    }
    
    // Arithmetic operations
    val bvadd = "bvadd" // addition
    val bvsub = "bvsub" // subtraction
    val bvneg = "bvneg" // unary minus
    val bvmul =  "bvmul" // multiplication
    val bvurem = "bvurem" // unsigned remainder
    val bvsrem = "bvsrem" // signed remainder
    val bvsmod = "bvsmod" // signed modulo
    val bvshl = "bvshl" // shift left
    val bvlshr = "bvlshr" // unsigned (logical) shift right
    val bvashr = "bvashr" // signed (arithmetical) shift right
    
    // Bitwise operations
    val bvor = "bvor" // bitwise or
    val bvand  = "bvand" // bitwise and
    val bvnot = "bvnot" // bitwise not
    val bvnand = "bvnand" // bitwise nand
    val bvnor = "bvnor" // bitwise nor
    val bvxnor = "bvxnor" // bitwise xnor
    
    // Special operations for internal use only
    val bvAddNoOverflowUnsigned = "bvAddNoOverflowUnsigned"
    val bvAddNoUnderflowSigned = "bvAddNoOverflowUnsigned"
    val bvAddNoUnderflow = "bvAddNoUnderflow"
    val bvSubNoOverflow = "bvSubNoOverflow"
    val bvSubNoUnderflowUnsigned = "bvSubNoUnderflowUnsigned"
    val bvSubNoUnderflowSigned = "bvSubNoUnderflowSigned"
    val bvSDivNoOverflow = "bvSDivNoOverflow"
    val bvNegNoOverflow = "bvNegNoOverflow"
    val bvMulNoOverflowUnsigned = "bvMulNoOverflowUnsigned"
    val bvMulNoUnderflowSigned = "bvMulNoUnderflowSigned"
    val bvMulNoUnderflow = "bvMulNoUnderflow"
    
    val binaryOperations: Set[String] = Set(
        bvadd, bvsub, bvmul, bvurem, bvsrem, bvsmod, bvshl, bvlshr, bvashr,
        bvor, bvand, bvnand, bvnor, bvxnor,
        bvAddNoOverflowUnsigned, bvAddNoUnderflowSigned, bvAddNoUnderflow,
        bvSubNoOverflow, bvSubNoUnderflowUnsigned, bvSubNoUnderflowSigned,
        bvSDivNoOverflow, bvMulNoOverflowUnsigned, bvMulNoUnderflowSigned,
        bvMulNoUnderflow
    ) 
    val unaryOperations: Set[String] = Set(
        bvneg, bvnot, bvNegNoOverflow
    )
}
