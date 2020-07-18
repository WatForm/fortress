package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.solverinterface._
import fortress.interpretation._
import fortress.operations._
import fortress.symmetry._

class FortressTWO_SI(solverStrategy: SolverStrategy) extends TransformationModelFinder(solverStrategy) {
    def this() = this(new Z3ApiSolver)
    
    override def transformerSequence(): Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new SortInferenceTransformer
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence ++= symmetryBreakingTransformers
        transformerSequence += QuantifierExpansionTransformer.create()
        transformerSequence += RangeFormulaTransformer.create()
        transformerSequence += new SimplifyTransformer
        transformerSequence += new DomainEliminationTransformer2
        transformerSequence.toList
    }
    
    def symmetryBreakingTransformers(): Seq[ProblemStateTransformer] = Seq(
        new SymmetryBreakingTransformerTWO(FunctionsFirstAnyOrder)
    )
}
