package fortress.compiler

import fortress.transformers._
import fortress.symmetry._

class NonDistUpperBoundCompiler extends LogicCompiler {

    // Only basics for now - need to validate optimizations work correctly
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer2
        transformerSequence += new DomainEliminationTransformer4
        transformerSequence.toList
    }

    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
    
}