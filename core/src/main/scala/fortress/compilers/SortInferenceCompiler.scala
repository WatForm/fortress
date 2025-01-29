package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer



class StandardSICompiler() extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.ListOfOne(
            new SymmetryBreakingTransformer(SymmetryBreakingOptions(
                selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
                breakSkolem = true,
                sortInference = true,
                patternOptimization = true,
            )))

}