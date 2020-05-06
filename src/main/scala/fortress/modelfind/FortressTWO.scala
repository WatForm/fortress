package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

class FortressTWO extends ModelFinderTemplate(new Z3ApiSolver) {
    override def transformerSequence(): Seq[TheoryTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[TheoryTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformerTWO(analysisScopes)
        transformerSequence += new DomainInstantiationTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new RangeFormulaTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new DomainEliminationTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new SimplifyTransformer
        transformerSequence.toList
    }
}
