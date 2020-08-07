package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.solverinterface._
import fortress.modelfind._
import fortress.symmetry._

class FortressTWOCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}