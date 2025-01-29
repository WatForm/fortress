package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to 
import fortress.transformers.Definitions.EliminateUnusedTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

class EvaluateCompiler extends StandardCompiler {
    override def quantifierHandler: ListBuffer[ProblemStateTransformer] = 
        // no QuantifiersToDefnsTransformer
        CompilersRegistry.ListOfOne(QuantifierExpansionTransformer)

    override def simplifiers: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += EvaluateTransformer
        ts += SimplifyTransformer
        ts += EliminateUnusedTransformer
        ts
    }
}