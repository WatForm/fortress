package fortress.solverinterface

import java.io._

import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

trait ProcessZ3ApiEvaluation extends ProcessBuilderSolver {

    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        object Solution extends Interpretation {
            override def constantInterpretations: Map[AnnotatedVar,Value] = Map()
            override def functionInterpretations: Map[FuncDecl,Map[Seq[Value],Value]] = Map()
            override def sortInterpretations: Map[Sort,Seq[Value]] = Map()
        }
        Solution
    }

}