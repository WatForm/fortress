package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._
import fortress.util.Errors

/** Replaces enum values with domain elements, following the mapping from the
  * computeEnumTypeMapping method. */
class EnumEliminationTransformer() extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
        val mapping = computeEnumTypeMapping(theory)
        
        // Since we are replacing with domain elements, which cannot be in
        // quantifiers, we do not need to worry about variable capture in
        // substitution and can use the faster substituter.
        val newAxioms = theory.axioms.map(axiom => axiom.recklessSubstitute(mapping))
        
        val newSignature = theory.signature.withoutEnums
        
        Theory.mkTheoryWithSignature(newSignature)
            .withScopes(theory.scopes)
            .withAxioms(newAxioms)
    }
    
    def computeEnumTypeMapping(theory: Theory): Map[Var, DomainElement] = {
        val mapping = scala.collection.mutable.Map[Var, DomainElement]()
        for((sort, enumConstants) <- theory.enumConstants) {
            enumConstants.zipWithIndex.foreach { case (constant, index) =>
                mapping += constant -> DomainElement(index + 1, sort)
            }
        }
        mapping.toMap
    }
    
    override def getName: String = "Enum Elimination Transformer"
}
