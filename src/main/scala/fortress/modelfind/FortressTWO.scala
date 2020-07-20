package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._

class FortressTWO(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder)
    )
}

class FortressTWO_BETA(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_BETA(FunctionsFirstAnyOrder)
    )
}

class FortressTWO_G(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstGreedy)
    )
}

class FortressTWO_R(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(Random)
    )
}

class FortressTWO_NoSymSkolem(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_NoSkolem(FunctionsFirstAnyOrder)
    )
}

class FortressTWO_Imp0(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_Imp0(FunctionsFirstAnyOrder)
    )
}

class FortressTWO_Imp1(solverStrategy: SolverStrategy) extends BaseFortress(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_Imp1(FunctionsFirstAnyOrder)
    )
}
