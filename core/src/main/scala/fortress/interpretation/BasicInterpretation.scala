package fortress.interpretation

import fortress.msfol._

/** An interpretation constructed by directly supplying the sort, constant, and function interpretations
  * to the constructor.
  */
class BasicInterpretation(
    val sortInterpretations: Map[Sort, Seq[Value]],
    val constantInterpretations: Map[AnnotatedVar, Value],
    val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
//    val functionDefinitions: Set[FunctionDefinition]
) extends Interpretation 

object BasicInterpretation {
    def apply(sortInterpretations: Map[Sort, Seq[Value]],
              constantInterpretations: Map[AnnotatedVar, Value],
              functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]],
              ): Interpretation =
        new BasicInterpretation(sortInterpretations, constantInterpretations, functionInterpretations)

    def empty: Interpretation = BasicInterpretation(Map.empty, Map.empty, Map.empty)
}

