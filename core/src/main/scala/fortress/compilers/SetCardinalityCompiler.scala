// should eventually integrate into the standard compiler

package fortress.compilers

//import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


class SetCardinalityCompiler extends StandardCompiler {

    override def setCardinalityOrNot: ListBuffer[ProblemStateTransformer] = {
        CompilersRegistry.ListOfOne(SetCardinalityTransformer)
    }
}