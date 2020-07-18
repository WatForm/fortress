package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._

class FortressTWO(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerTWO(FunctionsFirstAnyOrder)
    )
}

class FortressTWO_G(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerTWO(FunctionsFirstGreedy)
    )
}

class FortressTWO_R(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerTWO(Random)
    )
}
