package fortress.tfol

import scala.collection.immutable.Seq // Use immutable seq by default

trait SignatureExtension extends TypeCheckQuerying

// Cannot implement this as a mixin -- must implement as an object
object IntegerExtension extends SignatureExtension {
    
    // Builtin functions
    val plus = "+"
    val minus = "-"
    val times = "*"
    val div = "div"
    val mod = "mod"
    val LE = "<="
    val LT = "<"
    val GE = ">="
    val GT = ">"
    
    override def hasType(sort: Type): Boolean = sort == IntType
    
    override def hasTypeWithName(name: String): Boolean = name == IntType.name
    
    override def hasFunctionWithName(name: String): Boolean = 
        Set(plus, minus, times, div, mod, LE, LT, GE, GT) contains name
    
    override def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl] = (name, argTypes) match {
        case (`plus`, sorts) if sorts.length > 1 && sorts.forall(_ == IntType) => Some(FuncDecl(plus, sorts, IntType))
        case (`minus`, Seq(IntType, IntType)) => Some(FuncDecl(minus, IntType, IntType, IntType)) // Binary minus
        case (`minus`, Seq(IntType)) => Some(FuncDecl(minus, IntType, IntType)) // Unary minus
        case (`times`, Seq(IntType, IntType)) => Some(FuncDecl(times, IntType, IntType, IntType))
        case (`div`, Seq(IntType, IntType)) => Some(FuncDecl(div, IntType, IntType, IntType))
        case (`mod`, Seq(IntType, IntType)) => Some(FuncDecl(mod, IntType, IntType))
        case (`LE`, Seq(IntType, IntType)) => Some(FuncDecl(LE, IntType, IntType, BoolType))
        case (`LT`, Seq(IntType, IntType)) => Some(FuncDecl(LT, IntType, IntType, BoolType))
        case (`GE`, Seq(IntType, IntType)) => Some(FuncDecl(GE, IntType, IntType, BoolType))
        case (`GT`, Seq(IntType, IntType)) => Some(FuncDecl(GT, IntType, IntType, BoolType))
        case _ => None
    }
        
    override def queryConstant(v: Var): Option[AnnotatedVar] = None
    override def queryEnum(e: EnumValue): Option[Type] = None
    override def queryUninterpretedFunction(name: String): Option[FuncDecl] = None
    
    override def toString: String = "Integer Extension"
}

object BitVectorSignature {
    // Arithmetic operations
    val bvadd = "bvadd" // addition
    val bvsub = "bvsub" // subtraction
    val bvneg = "bvneg" // unary minus
    val bvmul =  "bvmul" // multiplication
    val bvsdiv = "bvsdiv" // signed division
    val bvsrem = "bvsrem" // signed remainder
    val bvsmod = "bvsmod" // signed modulo
    
    // // Special operations for internal use only
    // val bvAddNoOverflowSigned = "bvAddNoOverflowSigned"
    // val bvAddNoUnderflow = "bvAddNoOverflow" // For both signed and unsigned
    // 
    // val bvSubNoOverflow = "bvSubNoOverflow" // For both signed and unsigned
    // val bvSubNoUnderflowSigned = "bvSubNoUnderflowSigned"
    // 
    // val bvSDivNoOverflow = "bvSDivNoOverflow"
    // 
    // val bvNegNoOverflow = "bvNegNoOverflow"
    // 
    // val bvMulNoUnderflowSigned = "bvMulNoUnderflowSigned"
    // val bvMulNoUnderflow = "bvMulNoUnderflow"
    
    val binaryOperations: Set[String] = Set(
        bvadd, bvsub, bvmul, bvsdiv, bvsrem, bvsmod
    ) 
    val unaryOperations: Set[String] = Set(
        bvneg
    )
    
    def hasType(sort: Type):Boolean = sort match {
        case BitVectorType(_) => true
        case _ => false
    }
    
    def hasTypeWithName(name: String): Boolean = BitVectorType.namingPattern.findFirstIn(name).nonEmpty
    
    def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl] = (name, argTypes) match {
        case (binop, Seq(BitVectorType(n), BitVectorType(m)))
            if (binaryOperations contains binop) && (n == m) => Some( FuncDecl(binop, BitVectorType(n), BitVectorType(n), BitVectorType(n)) )
        case (unop, Seq(BitVectorType(n))) if (unaryOperations contains unop) => Some( FuncDecl(unop, BitVectorType(n), BitVectorType(n)) )
        case _ => None
    }
    
    def queryConstant(v: Var): Option[AnnotatedVar] = None
    def queryEnum(e: EnumValue): Option[Type] = None
    def queryUninterpretedFunction(name: String): Option[FuncDecl] = None
}
