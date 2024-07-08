package fortress.msfol
import scala.jdk.CollectionConverters._
import scala.annotation.varargs
import fortress.symmetry.Func
import fortress.util.Errors
/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))

  (define-fun max ((x Int) (y Int)) Int
    (ite (< x y) y x))
 */


case class FunctionDefinition(name: String, argSortedVar: Seq[AnnotatedVar], resultSort: Sort, body: Term) {
    Errors.Internal.precondition(argSortedVar.size > 0, "Cannot create nullary functions; use a constant instead")
    Errors.Internal.precondition(! Names.isIllegal(name), "Illegal function name " + name)
    Errors.Internal.precondition(name.length > 0, "Cannot create function with empty name")
    
    override def toString: String = {
        var str = name + " ("
        val n = argSortedVar.toList.size
        for (i <- 0 until n) {
            str += argSortedVar.toList(i).toString
            if (i < n - 1) {
                str += ", "
            }
        }
        str = str + "): " + resultSort.toString + " = { " + body.toString + "}\n"
        str
    }

    val argSorts: Seq[Sort] = argSortedVar.map(_.sort)

    def mapBody(f: Term => Term): FunctionDefinition = {
        FunctionDefinition(name, argSortedVar, resultSort, f(body))
    }
}

object FunctionDefinition {
    def mkFunctionDefinition(name:String, argSortedVar: java.util.List[AnnotatedVar], resultSort: Sort, body: Term): FunctionDefinition =
        FunctionDefinition(name, argSortedVar.asScala.toSeq , resultSort, body);
}


