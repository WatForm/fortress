package fortress.interpretation

import fortress.msfol._
import fortress.solverinterface._

abstract class ParserBasedInterpretation(signature: Signature) extends Interpretation {
    protected def getConstant(c: AnnotatedVar): Value
    protected def getSort(s: Sort): Seq[Value]
    protected def getFunctionDefinitions: Set[FunctionDefinition]
    protected def getFunctionValues(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value]

    protected def scopes: Map[Sort, Int] = for((sort, seq) <- sortInterpretations) yield (sort -> seq.size)

}
