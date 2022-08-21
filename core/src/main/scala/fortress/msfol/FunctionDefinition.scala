package fortress.msfol
import scala.jdk.CollectionConverters._
import scala.annotation.varargs
/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))
 */


case class FunctionDefinition(name: String, argSortedVar: Set[AnnotatedVar], resultSort: Sort, body: Term) {
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
}

object FunctionDefinition {
    def mkFunctionDefinition(name:String, argSortedVar: java.util.Set[AnnotatedVar], resultSort: Sort, body: Term): FunctionDefinition =
        FunctionDefinition(name, argSortedVar.asScala.toSet , resultSort, body);
}


