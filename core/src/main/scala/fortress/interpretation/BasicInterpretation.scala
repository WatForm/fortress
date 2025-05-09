package fortress.interpretation

import fortress.msfol._

import scala.jdk.CollectionConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import scala.jdk.OptionConverters._
import scala.util.Using

/** An interpretation constructed by directly supplying the sort, constant, and function interpretations
  * to the constructor.
  */
class BasicInterpretation private (
    val sortInterpretations: Map[Sort, Seq[Value]],
    val constantInterpretations: Map[AnnotatedVar, Value],
    override val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]],
    val functionDefinitions: Set[FunctionDefinition]
) extends Interpretation {
  if (!functionInterpretations.isEmpty) {
    fortress.util.Errors.Internal.impossibleState
  }
}

object BasicInterpretation {
    def apply(sortInterpretations: Map[Sort, Seq[Value]],
              constantInterpretations: Map[AnnotatedVar, Value],
              functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]],
              functionDefinitions: Set[FunctionDefinition]
              ): Interpretation = {
                new BasicInterpretation(sortInterpretations, constantInterpretations, functionInterpretations, functionDefinitions)
              }

    def empty: Interpretation = BasicInterpretation(Map.empty, Map.empty, Map.empty, Set.empty)

}

