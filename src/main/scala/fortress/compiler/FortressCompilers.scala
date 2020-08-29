package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.modelfind._
import fortress.symmetry._

class FortressZEROCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq.empty
}

class FortressONECompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(AtoAOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_SI(integerSemantics: IntegerSemantics) extends TransformationCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
    
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new TypecheckSanitizeTransformer
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new SortInferenceTransformer
        transformerSequence += new TypecheckSanitizeTransformer
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer.create()
        transformerSequence += new SimplifyTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}

class FortressTHREECompiler(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTHREECompiler_SI(integerSemantics: IntegerSemantics) extends TransformationCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerSI(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new TypecheckSanitizeTransformer
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new SortInferenceTransformer
        transformerSequence += new TypecheckSanitizeTransformer
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer.create()
        transformerSequence += new SimplifyTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}