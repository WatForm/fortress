package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer

class FortressZERO(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3ApiInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq.empty
}
