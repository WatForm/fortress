package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemTransformer

class FortressZERO extends BaseFortress {
    override def symmetryBreakingTransformers(): Seq[ProblemTransformer] = Seq.empty
}
