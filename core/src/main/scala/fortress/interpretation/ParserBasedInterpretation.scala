package fortress.interpretation

import fortress.msfol._
import fortress.solverinterface._

abstract class ParserBasedInterpretation(signature: Signature, scopeMap: Map[Sort, Scope]) extends EvaluationBasedInterpretation(signature) {
    override val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = {
        if( signature.sorts.size == scopes.size ) {
            // TODO: use ruomei's method
            Map.empty
        }.toMap
        else {
            Map.empty
        }
    }
}
