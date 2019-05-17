package fortress.msfol

import fortress.util.Errors
import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // Default to immutable Seqs
import scala.annotation.varargs // So we can call Scala varargs methods from Java

case class FuncDecl(name: String, argSorts: Seq[Sort], resultSort: Sort) {
    Errors.precondition(argSorts.size > 0, "Cannot create nullary functions; use a constant instead")
    Errors.precondition(! Names.isIllegal(name), "Illegal function name " + name)
    Errors.precondition(name.length > 0, "Cannot create function with empty name")
    
    def getArity: Int = argSorts.size

    def getName: String = name

    def getArgSorts: java.util.List[Sort] = argSorts.asJava

    def getResultSort: Sort = resultSort
    
    override def toString: String = name + ": (" + argSorts.mkString(", ") + ") -> " + resultSort.toString
}

object FuncDecl {
    def apply(name: String, sorts: Sort*): FuncDecl = FuncDecl(name, sorts.take(sorts.size - 1).toList, sorts.last)
    
    def mkFuncDecl(name: String, argSorts: java.util.List[Sort], resultSort: Sort): FuncDecl =
        FuncDecl(name, argSorts.asScala.toList, resultSort)
    
    @varargs
    def mkFuncDecl(name: String, sorts: Sort*): FuncDecl = {
        val argSorts = new scala.collection.mutable.ListBuffer[Sort]
        val resultSort = sorts(sorts.size - 1);
        for(i <- 0 to (sorts.size - 2)) {
            argSorts += sorts(i)
        }
        FuncDecl(name, argSorts.toList, resultSort);
    }
}
