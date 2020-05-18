package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import scala.language.implicitConversions
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemTransformer
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

class FortressZERO extends BaseFortress {
    override def symmetryBreakingTransformers(): Seq[ProblemTransformer] = Seq.empty
}
