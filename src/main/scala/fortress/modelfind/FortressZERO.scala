package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemTransformer

class FortressZERO(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemTransformer] = Seq.empty
}
