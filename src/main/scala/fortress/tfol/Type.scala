package fortress.tfol

import fortress.util.Errors

/** Represents a type, sometimes called a sort. */
case class Type(name: String) {
    Errors.precondition(name.length > 0, "Cannot create type with empty name");
    Errors.precondition(! Names.isIllegal(name), "Illegal type name " + name);
    
    def getName: String = name
    override def toString: String = name
}

object Type {
    def mkTypeConst(name: String): Type = Type(name)
    val Bool: Type = mkTypeConst("Bool")
}
