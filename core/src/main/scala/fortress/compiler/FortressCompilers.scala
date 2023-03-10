package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


abstract class ConstantsMethodCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }

}

abstract class DatatypeMethodNoRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

}

abstract class DatatypeMethodWithRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

}



/**
  * The standard Fortress compiler steps.
  */
abstract class BaseFortressCompiler() extends LogicCompiler {
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

abstract class BaseFortressCompilerEnums() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += IntegerToBitVectorTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

    def symmetryBreakingTransformers: Seq[ProblemStateTransformer]
}


class FortressZEROCompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq.empty
}

class FortressONECompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_SI() extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
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

class FortressTHREECompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTHREECompiler_SI() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressFOURCompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )
}

class FortressFOURCompiler_SI() extends LogicCompiler {
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

class FortressUnboundedCompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += IntegerToBitVectorTransformer
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
}

class FortressLearnedLiteralsCompiler() extends BaseFortressCompiler() {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += IntegerToBitVectorTransformer
//        transformerSequence += ClosureEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
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
        transformerSequence += RangeFormulaStandardTransformer
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
        transformerSequence += ScopeNonExactPredicatesTransformer // Must be before skolemization
        transformerSequence += EnumEliminationTransformer
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

/**
  * A compiler designed to allow manual addition of transformers to the transformer sequence
  *
  */
class ConfigurableCompiler(transformers: ListBuffer[ProblemStateTransformer]) extends LogicCompiler {
    def this() {
        this(new collection.mutable.ListBuffer[ProblemStateTransformer])
    }
    def this(transformers: Seq[ProblemStateTransformer]){
        this(ListBuffer.from(transformers))
    }
    def this(transformers: Array[ProblemStateTransformer]){
        this(ListBuffer.from(transformers.toSeq))
    }
    override def transformerSequence: Seq[ProblemStateTransformer] = transformers.toList

    def addTransformer(transformer: ProblemStateTransformer): Unit = {
        transformers += transformer
    }

    def addTransformers(newTransformers: Seq[ProblemStateTransformer]): Unit = {
        transformers ++= newTransformers
    }
}

class IncrementalCompiler extends LogicCompiler {
//    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
//        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
//    )
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
//        transformerSequence += ScopeNonExactPredicatesTransformer // Must be before skolemization
        transformerSequence += EnumEliminationTransformer
        transformerSequence += ClosureEliminationEijckTransformer
//        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += IncrementalRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence += AddScopeConstraintsTransformer //***//
        transformerSequence.toList
    }
}

class MonotonicityCompiler extends LogicCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_MostUsed(LowArityFirstMostUsedFunctionFirstOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
    )
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += MergeMonotonicSortsTransformer // *** //
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += IncrementalRangeFormulaTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence += AddScopeConstraintsTransformer
        transformerSequence.toList
    }
}
