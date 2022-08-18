package fortress.msfol

/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))
 */


case class FunctionDefinition(name: String, argSortedVar: Set[AnnotatedVar], resultSort: Sort, body: Term) {
    override def toString: String = {
        var str = name + " ("
        argSortedVar.foreach(arg => {
            str += arg.toString + ", "
        })
        str = str + "): " + resultSort.toString + " = " + body.toString
        str
    }
}


