package fortress.interpretation

import fortress.msfol._

class BasicInterpretation(
    val sortInterpretations: Map[Sort, Seq[Value]],
    val constantInterpretations: Map[AnnotatedVar, Value],
    val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
) extends Interpretation
