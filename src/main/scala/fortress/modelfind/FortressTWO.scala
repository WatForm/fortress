package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._

class FortressTWO(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWO_G(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstGreedy, DefaultSymmetryBreaker)
    )
}

class FortressTWO_R(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(Random, DefaultSymmetryBreaker)
    )
}

class FortressTWO_P(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWO_PG(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesFirstGreedy, DefaultSymmetryBreaker)
    )
}

class FortressTWO_PO(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(PredicatesOnlyAnyOrder, DefaultSymmetryBreaker)
    )
}

// Constants only
class FortressTWO_CO(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(NoFunctionsPredicates, DefaultSymmetryBreaker)
    )
}

class FortressTWO_NoSymSkolem(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer_NoSkolem(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWO_Imp0(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Imp0SymmetryBreaker)
    )
}

class FortressTWO_Imp1(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Imp1SymmetryBreaker)
    )
}

class FortressTWO_NoElision(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def transformerSequence(): Seq[ProblemStateTransformer] = {
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
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

// Have to use NoElision for range formulas, since the shortened one is not generated.
class FortressTWO_Neq0(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def transformerSequence(): Seq[ProblemStateTransformer] = {
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
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Neq0SymmetryBreaker)
    )
}

class FortressTWO_Neq1(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, Neq1SymmetryBreaker)
    )
}

class FortressTWO_SR(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def transformerSequence(): Seq[ProblemStateTransformer] = {
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
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, DefaultSymmetryBreaker)
    )
}

class FortressTWO_RAINBOW(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, RainbowSymmetryBreaker)
    )
}

class FortressTWO_US(solverInterface: SolverInterface) extends BaseFortress(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformer(FunctionsFirstAnyOrder, UsedFirstRidSymmetryBreaker)
    )
}