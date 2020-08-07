package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.modelfind._
import fortress.symmetry._

class FortressONECompiler_UNS(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(AtoAOnlyAnyOrder, UnusedFirstRidSymmetryBreaker)
    )
}

class FortressTWOCompiler_UNS(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, UnusedFirstRidSymmetryBreaker)
    )
}

class FortressTWOCompiler_G(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstGreedy, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_R(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(Random, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_P(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_PG(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesFirstGreedy, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_PO(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

// Constants only
class FortressTWOCompiler_CO(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(NoFunctionsPredicates, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_NoSymSkolem(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_NoSkolem(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWOCompiler_Imp0(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Imp0SymmetryBreaker)
    )
}

class FortressTWOCompiler_Imp1(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Imp1SymmetryBreaker)
    )
}

class FortressTWOCompiler_NoElision(integerSemantics: IntegerSemantics) extends TransformationCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer_NoElision.create()
        transformerSequence += new SimplifyTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}

// Have to use NoElision for range formulas, since the shortened one is not generated.
class FortressTWOCompiler_Neq0(integerSemantics: IntegerSemantics) extends TransformationCompiler {
    def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Neq0SymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer_NoElision.create()
        transformerSequence += new SimplifyTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}

class FortressTWOCompiler_Neq1(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Neq1SymmetryBreaker)
    )
}

class FortressTWOCompiler_SR(integerSemantics: IntegerSemantics) extends TransformationCompiler {
    val symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )

    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer.create()
        transformerSequence += new SimplifyWithRangeTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
}

class FortressTWOCompiler_RAINBOW(integerSemantics: IntegerSemantics) extends BaseFortressCompiler(integerSemantics) {
    override def symmetryBreakingTransformers: Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, RainbowSymmetryBreaker)
    )
}