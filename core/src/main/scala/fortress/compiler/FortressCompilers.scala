package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

/* 
    using constants for DEs
    have to get rid of quantifiers (skolemize, quant exp)
    need range formulas
*/
abstract class ConstantsMethodCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer
        // transformerSequence += IntegerToBitVectorTransformer    
        transformerSequence += OPFIIntsTransformer 
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += QuantifiersToDefinitionsTransformer
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }

}

/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no nnf, no skolemization and no quantifier expansion)
   no range formulas (b/c datatype limits output to finite)
*/
abstract class DatatypeMethodNoRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        // transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer
        // transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += OPFIIntsTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += QuantifiersToDefinitionsTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

}

/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no nnf, no skolemize/quantifier expansion)
   use range formulas 
*/
abstract class DatatypeMethodWithRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        // transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer
        // transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += OPFIIntsTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += QuantifiersToDefinitionsTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

}

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (nnf, skolemize, quant exp)
   don't use range formulas (b/c datatype limits output to finite)
*/
abstract class DatatypeMethodNoRangeEUFCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer
        // transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += OPFIIntsTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += QuantifiersToDefinitionsTransformer
        transformerSequence += StandardQuantifierExpansionTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }

}

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (skolemize, quant exp)
   include range formulas
*/
abstract class DatatypeMethodWithRangeEUFCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer
        // transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += OPFIIntsTransformer
        transformerSequence += NnfTransformer
        transformerSequence += SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += QuantifiersToDefinitionsTransformer
        transformerSequence += StandardQuantifierExpansionTransformer
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
        transformerSequence += EnumEliminationTransformer
        transformerSequence += SortInferenceTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ScopeNonExactPredicatesTransformer // Must be before skolemization
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

