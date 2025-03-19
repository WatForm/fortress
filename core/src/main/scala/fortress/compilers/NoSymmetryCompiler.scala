package fortress.compilers

import fortress.transformers._ // for implicit conversion to ProblemStateTransformer
import scala.collection.mutable.ListBuffer


class NoSymmetryCompiler extends StandardCompiler {
    override def symmetryBreaker: ListBuffer[ProblemStateTransformer] = CompilersRegistry.NullTransformerList
}
