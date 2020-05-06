package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import scala.language.implicitConversions
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemTransformer
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._


class FortressZERO extends ModelFinderTemplate(new Z3ApiSolver) {
    override def transformerSequence(): Seq[ProblemTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemTransformer]
        transformerSequence += new EnumEliminationTransformer
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        // No symmetry breaking
        transformerSequence += new DomainInstantiationTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new RangeFormulaTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new DomainEliminationTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new SimplifyTransformer
        transformerSequence.toList
    }
}
