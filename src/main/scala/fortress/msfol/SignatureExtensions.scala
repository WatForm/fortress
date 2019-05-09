package fortress.msfol

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
    
    override def hasSort(sort: Sort): Boolean = (sort == IntSort)
    
    override def hasSortWithName(name: String): Boolean = (name == IntSort.name)
    
    override def hasFunctionWithName(name: String): Boolean = 
        Set(plus, minus, times, div, mod, LE, LT, GE, GT) contains name
    
    override def queryFunction(name: String, argSorts: Seq[Sort]): Option[FuncDecl] = (name, argSorts) match {
        case (`plus`, sorts) if sorts.length > 1 && sorts.forall(_ == IntSort) => Some(FuncDecl(plus, sorts, IntSort))
        case (`minus`, Seq(IntSort, IntSort)) => Some(FuncDecl(minus, IntSort, IntSort, IntSort)) // Binary minus
        case (`minus`, Seq(IntSort)) => Some(FuncDecl(minus, IntSort, IntSort)) // Unary minus
        case (`times`, Seq(IntSort, IntSort)) => Some(FuncDecl(times, IntSort, IntSort, IntSort))
        case (`div`, Seq(IntSort, IntSort)) => Some(FuncDecl(div, IntSort, IntSort, IntSort))
        case (`mod`, Seq(IntSort, IntSort)) => Some(FuncDecl(mod, IntSort, IntSort))
        case (`LE`, Seq(IntSort, IntSort)) => Some(FuncDecl(LE, IntSort, IntSort, BoolSort))
        case (`LT`, Seq(IntSort, IntSort)) => Some(FuncDecl(LT, IntSort, IntSort, BoolSort))
        case (`GE`, Seq(IntSort, IntSort)) => Some(FuncDecl(GE, IntSort, IntSort, BoolSort))
        case (`GT`, Seq(IntSort, IntSort)) => Some(FuncDecl(GT, IntSort, IntSort, BoolSort))
        case _ => None
    }
        
    override def queryConstant(v: Var): Option[AnnotatedVar] = None
    override def queryEnum(e: EnumValue): Option[Sort] = None
    override def queryUninterpretedFunction(name: String): Option[FuncDecl] = None
    
    override def toString: String = "Integer Extension"
}

object BitVectorExtension extends SignatureExtension {
    // Arithmetic operations
    val bvadd = "bvadd" // addition
    val bvsub = "bvsub" // subtraction
    val bvneg = "bvneg" // unary minus
    val bvmul =  "bvmul" // multiplication
    val bvsdiv = "bvsdiv" // signed division
    val bvsrem = "bvsrem" // signed remainder
    val bvsmod = "bvsmod" // signed modulo
    
    //Comparison operations
    val bvslt = "bvslt" // Signed less than
    val bvsle = "bvsle" // Signed less than or equal
    val bvsgt = "bvsgt" // Signed greater than
    val bvsge = "bvsge" // Signed greater than or equal
    
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
    
    val comparisonOperations: Set[String] = Set(
        bvslt, bvsle, bvsgt, bvsge
    )
    
    def hasSort(sort: Sort):Boolean = sort match {
        case BitVectorSort(_) => true
        case _ => false
    }
    
    def hasSortWithName(name: String): Boolean = BitVectorSort.namingPattern.findFirstIn(name).nonEmpty
    
    def queryFunction(name: String, argSorts: Seq[Sort]): Option[FuncDecl] = (name, argSorts) match {
        case (binop, Seq(BitVectorSort(n), BitVectorSort(m)))
            if (binaryOperations contains binop) && (n == m) => Some( FuncDecl(binop, BitVectorSort(n), BitVectorSort(n), BitVectorSort(n)) )
        case (unop, Seq(BitVectorSort(n))) if (unaryOperations contains unop) => Some( FuncDecl(unop, BitVectorSort(n), BitVectorSort(n)) )
        case _ => None
    }
    
    def hasFunctionWithName(name: String): Boolean = 
        ((binaryOperations union unaryOperations) union comparisonOperations) contains name
    
    def queryConstant(v: Var): Option[AnnotatedVar] = None
    def queryEnum(e: EnumValue): Option[Sort] = None
    def queryUninterpretedFunction(name: String): Option[FuncDecl] = None
}
