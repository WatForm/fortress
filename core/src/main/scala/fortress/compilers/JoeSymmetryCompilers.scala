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
        transformerSequence += EnumsToDEsTransformer
        transformerSequence += IntToBVTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        
        // the next one was not in Joe's original tests for symmetry but
        // now must be run before NnfTransformer or there are warnings
        transformerSequence += IfLiftingTransformer

        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += DEsToDistinctConstantsTransformer
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
        transformerSequence += EnumsToDEsTransformer
        transformerSequence += IntToBVTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += DEsToDistinctConstantsTransformer
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
        new SymmetryBreakingTransformer(SymmetryBreakingOptions(MonoFirstThenFunctionsFirstAnyOrder, breakSkolem = true, sortInference = true, patternOptimization = false, 
            disjLimit= None))
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
        transformerSequence += EnumsToDEsTransformer
        transformerSequence += IntToBVTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer
        transformerSequence += RangeFormulaUseDEsTransformer
        transformerSequence += SimplifyTransformer
        transformerSequence += DEsToDistinctConstantsTransformer
        transformerSequence.toList
    }
}