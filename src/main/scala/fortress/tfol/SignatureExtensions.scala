package fortress.tfol

import scala.collection.immutable.Seq // Use immutable seq by default

trait SignatureExtension extends TypeCheckQuerying {
    override def queryUninterpretedFunction(name: String): Option[FuncDecl] = None
}

// Cannot implement this as a mixin -- must implement as an object
object IntegerExtension extends SignatureExtension {
    
    // Builtin functions
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
    override def queryEnum(v: Var): Option[AnnotatedVar] = None
    
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
