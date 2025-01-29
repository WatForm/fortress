package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

class EijckCompiler() extends StandardCompiler {

    override def closureEliminator: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(ClosureEliminationEijckTransformer)

}