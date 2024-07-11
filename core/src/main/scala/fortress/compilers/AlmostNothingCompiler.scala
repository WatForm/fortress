package fortress.compilers

//import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

class AlmostNothingCompiler extends BaseCompiler {

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = NullTransformerList
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumsToDEsTransformer
        transformerSequence += DEsToDistinctConstantsTransformer
        transformerSequence.toList
	}
}