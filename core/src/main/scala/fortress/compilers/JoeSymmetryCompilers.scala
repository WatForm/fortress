package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

/**
  * The standard Joe compiler steps.
  */
abstract class BaseJoeSymmetryCompiler() extends Compiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += LiaCheckTransformer
        transformerSequence += IntegerToBitVectorTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }

    def symmetryBreakingTransformers: Seq[ProblemStateTransformer]
}


class JoeZEROCompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq.empty
}

class JoeONECompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoOnlyAnyOrder)
    )
}

class JoeTWOCompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder)
    )
}

class JoeTWO_SICompiler() extends BaseJoeSymmetryCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += IntegerToBitVectorTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class JoeTHREECompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder)
    )
}

class JoeTHREE_SICompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(SymmetryBreakingOptions(MonoFirstThenFunctionsFirstAnyOrder, breakSkolem = true, sortInference = true, patternOptimization = false))
    )
}

class JoeFOURCompiler() extends BaseJoeSymmetryCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )
}

class JoeFOUR_SICompiler() extends BaseJoeSymmetryCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += IntegerToBitVectorTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}