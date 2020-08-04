package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._

class FortressONE(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(AtoAOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressONE_US(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(AtoAOnlyAnyOrder, UsedFirstRidSymmetryBreaker)
    )
}