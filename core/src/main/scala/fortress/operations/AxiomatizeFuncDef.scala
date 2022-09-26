package fortress.operations

import fortress.msfol._

object AxiomatizeFuncDef {

    def axiomatize(funcDef: FunctionDefinition): Term = {
        val argList: Seq[AnnotatedVar] = funcDef.argSortedVar
        val axiomBody = funcDef.body

    }

}
