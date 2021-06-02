package fortress.interpretation

import fortress.msfol._

/** An interpretation constructed by directly supplying the sort, constant, and function interpretations
  * to the constructor.
  */
class BasicInterpretation(
    val sortInterpretations: Map[Sort, Seq[Value]],
    val constantInterpretations: Map[AnnotatedVar, Value],
    val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
) extends Interpretation

