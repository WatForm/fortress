package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer



class MaxUnboundedScopesCompiler extends StandardCompiler {
    override def scopes: ListBuffer[ProblemStateTransformer] = {
        val ts:ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.NullTransformerList
        ts += MaxUnboundedScopesTransformer
        ts += ScopeNonExactPredicatesTransformer
        ts
    }
}