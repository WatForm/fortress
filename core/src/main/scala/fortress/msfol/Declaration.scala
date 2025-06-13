package fortress.msfol

import fortress.util.Errors
import scala.jdk.CollectionConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import fortress.util.NameConverter

/** A constant or function declaration, with sorts */
sealed trait Declaration {
    def name: String
}


/** A function declaration, including name, argument sorts, and result sort. */
case class FuncDecl private (name: String, argSorts: Seq[Sort], resultSort: Sort) extends Declaration {
    Errors.Internal.precondition(argSorts.size > 0, "Cannot create nullary functions; use a constant instead")
    Errors.Internal.precondition(! Names.isIllegal(name), "Illegal function name " + name)
    Errors.Internal.precondition(name.length > 0, "Cannot create function with empty name")
    
    /** The number of argument sorts. */
    def arity: Int = argSorts.size

    /** Whether the function is range-domain dependent (the result sort is one of the argument sorts). */
    def isRDD: Boolean = argSorts contains resultSort

    /** Whether the function is range-domain independent (the result sort is not one of the argument sorts). */
    def isRDI: Boolean = !isRDD

    /** Whether all sorts, both argument and result, of the function are the same, and the sort is not builtin. */ 
    def isMonoSorted: Boolean = argSorts.forall(_ == resultSort) && !resultSort.isBuiltin
    
    /** Whether all sorts, both argument and result, of the function are distinct. */
    def isRainbowSorted: Boolean = isRDI && (argSorts.distinct == argSorts)

    def allSorts: Seq[Sort] = argSorts :+ resultSort
    
    override def toString: String = name + ": (" + argSorts.mkString(", ") + ") -> " + resultSort.toString
}

/** Factory for [[fortress.msfol.FuncDecl]] instances. */
object FuncDecl {
    def apply(name: String, sorts: Sort*): FuncDecl = {
        val unquotedName = NameConverter.nameWithoutQuote(name)
        FuncDecl(unquotedName, sorts.take(sorts.size - 1).toList, sorts.last)
    }
    def mkFuncDecl(name: String, argSorts: java.util.List[Sort], resultSort: Sort): FuncDecl = {
        val unquotedName = NameConverter.nameWithoutQuote(name)
        FuncDecl(unquotedName, argSorts.asScala.toList, resultSort)
    }
        
    
    @varargs
    def mkFuncDecl(name: String, sorts: Sort*): FuncDecl = {
        val argSorts = new scala.collection.mutable.ListBuffer[Sort]
        val resultSort = sorts(sorts.size - 1);
        for(i <- 0 to (sorts.size - 2)) {
            argSorts += sorts(i)
        }
        val unquotedName = NameConverter.nameWithoutQuote(name)
        FuncDecl(unquotedName, argSorts.toList, resultSort);
    }
}

/** A variable together with a sort annotation.
  * Used in quantifiers and constant declarations.
  * Note: AnnotatedVar is not a subclass of Term;
  * inside a Term it is only possible (and required) to annotate a Var when
  * a quantifier declares it bound.
  */
case class AnnotatedVar (variable: Var, sort: Sort) extends Declaration {
    def name: String = variable.name
    
    override def toString: String = variable.toString + ": " + sort.toString
}