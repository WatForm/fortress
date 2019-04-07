package fortress.tfol

import fortress.util.Errors
import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // Default to immutable Seqs
import scala.annotation.varargs // So we can call Scala varargs methods from Java

case class FuncDecl(name: String, argTypes: Seq[Type], resultType: Type) {
    Errors.precondition(argTypes.size > 0, "Cannot create nullary functions; use a constant instead")
    Errors.precondition(! Names.isIllegal(name), "Illegal function name " + name)
    Errors.precondition(name.length > 0, "Cannot create function with empty name")
    
    def getArity: Int = argTypes.size
    
    def getName: String = name
    
    def getArgTypes: java.util.List[Type] = argTypes.asJava
    
    def getResultType: Type = resultType
    
    override def toString: String = name + ": (" + argTypes.mkString(", ") + ") -> " + resultType.toString
}

object FuncDecl {
    def mkFuncDecl(name: String, argTypes: java.util.List[Type], resultType: Type): FuncDecl =
        FuncDecl(name, argTypes.asScala.toList, resultType)
    
    @varargs
    def mkFuncDecl(name: String, types: Type*): FuncDecl = {
        val argTypes = new scala.collection.mutable.ListBuffer[Type]
        val resultType = types(types.size - 1);
        for(i <- 0 to (types.size - 2)) {
            argTypes += types(i)
        }
        FuncDecl(name, argTypes.toList, resultType);
    }
}
