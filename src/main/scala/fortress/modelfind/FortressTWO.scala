package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer

class FortressTWO extends BaseFortress {
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerTWO
    )
}
