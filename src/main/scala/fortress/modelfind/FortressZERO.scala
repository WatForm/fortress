package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer

class FortressZERO extends BaseFortress {
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq.empty
}
