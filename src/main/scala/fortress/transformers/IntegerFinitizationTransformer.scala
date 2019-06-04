package fortress.transformers

import scala.collection.JavaConverters._

import fortress.msfol._
import fortress.util.Errors

class IntegerFinitizationTransformer(bitwidth: Int) extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {
        val newAxioms = theory.axioms.map(_.finitizeIntegers(bitwidth))
        val newSig = theory.signature.replaceIntegersWithBitVectors(bitwidth)
        Theory.mkTheoryWithSignature(newSig).withAxioms(newAxioms)
    }
    
    override val name: String = "Integer Finitization Transformer"
}
