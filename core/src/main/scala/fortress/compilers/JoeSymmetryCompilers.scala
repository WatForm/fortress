package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

/**
  * The standard Joe compiler steps.
  */
abstract class BaseJoeSymmetryCompiler() extends BaseCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += LiaCheckTransformer
        transformerSequence += IntToBVTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += ConstantsForDEsDistinctTransformer
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
        transformerSequence += IntToBVTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += ConstantsForDEsDistinctTransformer
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
        transformerSequence += IntToBVTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += ConstantsForDEsDistinctTransformer
        transformerSequence.toList
    }
}