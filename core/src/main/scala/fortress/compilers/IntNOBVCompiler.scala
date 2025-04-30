// should eventually integrate into the standard compiler

package fortress.compilers

//import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


class IntNOBVCompiler extends StandardCompiler {

    override def integerHandler: ListBuffer[ProblemStateTransformer] = {
        CompilersRegistry.ListOfOne(IntNOBVTransformer)
    }
}
