package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.modelfind._
import fortress.symmetry._

/**
  * The standard Fortress compiler steps.
  *
  * @param integerSemantics which IntegerSemantics to use
  */
abstract class BaseFortressCompiler(integerSemantics: IntegerSemantics) extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
//        integerSemantics match {
//            case Unbounded => ()
//            case ModularSigned(bitwidth) => {
//                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
//            }
//        }
//        transformerSequence += ClosureEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }

    def symmetryBreakingTransformers: Seq[ProblemStateTransformer]
}

class FortressZEROCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq.empty
}

class FortressONECompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_SI(integerSemantics: IntegerSemantics) extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
//        integerSemantics match {
//            case Unbounded => ()
//            case ModularSigned(bitwidth) => {
//                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
//            }
//        }
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class FortressTHREECompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTHREECompiler_SI(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressFOURCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )
}

class FortressFOURCompiler_SI(integerSemantics: IntegerSemantics) extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
//        integerSemantics match {
//            case Unbounded => ()
//            case ModularSigned(bitwidth) => {
//                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
//            }
//        }
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class FortressUnboundedCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
//        integerSemantics match {
//            case Unbounded => ()
//            case ModularSigned(bitwidth) => {
//                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
//            }
//        }
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class FortressLearnedLiteralsCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
//        integerSemantics match {
//            case Unbounded => ()
//            case ModularSigned(bitwidth) => {
//                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
//            }
//        }
//        transformerSequence += ClosureEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += SplitConjunctionTransformer
        transformerSequence += new SimplifyLearnedLiteralsTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class NonDistUpperBoundCompiler extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )

    // Only basics for now - need to validate optimizations work correctly
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer2
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}

class PredUpperBoundCompiler extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )

    // Only basics for now - need to validate optimizations work correctly
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += new ScopeSubtypeTransformer // Must be before skolemization
        transformerSequence += EnumEliminationTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += StandardRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}
