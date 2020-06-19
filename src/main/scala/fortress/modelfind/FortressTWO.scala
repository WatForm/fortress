package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemTransformer

class FortressTWO extends BaseFortress {
    override def symmetryBreakingTransformers(): Seq[ProblemTransformer] = Seq(
        new SymmetryBreakingTransformerTWO
    )
}
