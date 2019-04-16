package fortress.tfol

import fortress.util.Errors

/** Represents a type (or sort if your prefer). */
sealed abstract class Type {
    def name: String
    def getName: String = name
    def isBuiltin: Boolean
    override def toString: String = name
}

case class TypeConst private (name: String) extends Type {
    Errors.precondition(name.length > 0, "Cannot create type with empty name");
    Errors.precondition(! Names.isIllegal(name), "Illegal type name " + name);
    Errors.precondition(! name.contains(" "), "Cannot make type constant with space " + name)
    Errors.precondition(! Type.nameMimicsBuiltin(name), "Cannot make type constant with name " + name)
    
    override def isBuiltin: Boolean = false
}

case object BoolType extends Type {
    def name: String = "Bool"
    override def isBuiltin: Boolean = true
}

case object IntType extends Type {
    def name: String = "Int"
    override def isBuiltin: Boolean = true
}

case object RealType extends Type {
    def name: String = "Real"
    override def isBuiltin: Boolean = true
}

case class BitVectorType(bitwidth: Int) extends Type {
    def name: String = "BitVec " + bitwidth.toString
    override def isBuiltin: Boolean = true
}

object Type {
    def mkTypeConst(name: String): Type = TypeConst(name)
    
    val Bool: Type = BoolType
    val Int: Type = IntType
    val Real: Type = RealType
    def BitVector(bitwidth: Int) = BitVectorType(bitwidth)
    
    def nameMimicsBuiltin(name: String) = {
        name == "Bool" || name == "Int" || name == "Real" || name.startsWith("BitVec")
    }
}
