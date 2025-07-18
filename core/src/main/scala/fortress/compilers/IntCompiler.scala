/* 
 * a compiler that takes an integer problem state transformer
 * as an argument and makes a compiler that varies only in
 * integer transformer from the standard compiler
 */

package fortress.compilers

//import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


class IntCompiler (
    intTransformer: ProblemStateTransformer
) extends StandardCompiler {

  override def integerHandler:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(intTransformer)

}