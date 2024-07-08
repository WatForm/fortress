/**
  * A compiler designed to allow manual addition of transformers to the transformer sequence
  *
  */


package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

class ConfigurableCompiler(transformers: ListBuffer[ProblemStateTransformer]) extends BaseCompiler {
    def this() {
        this(new collection.mutable.ListBuffer[ProblemStateTransformer])
    }
    def this(transformers: Seq[ProblemStateTransformer]){
        this(ListBuffer.from(transformers))
    }
    def this(transformers: Array[ProblemStateTransformer]){
        this(ListBuffer.from(transformers.toSeq))
    }
    override def transformerSequence: Seq[ProblemStateTransformer] = transformers.toList

    def addTransformer(transformer: ProblemStateTransformer): Unit = {
        transformers += transformer
    }

    def addTransformers(newTransformers: Seq[ProblemStateTransformer]): Unit = {
        transformers ++= newTransformers
    }
}