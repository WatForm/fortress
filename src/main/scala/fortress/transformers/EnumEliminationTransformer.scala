package fortress.transformers

import scala.collection.JavaConverters._

import fortress.msfol._
import fortress.util.Errors

/** Replaces enum values with domain elements, following the mapping from the
  * computeEnumSortMapping method. */
class EnumEliminationTransformer() extends TheoryTransformer {
    override def apply(theory: Theory): Theory = {
        val mapping = computeEnumSortMapping(theory)
        
        // Since we are replacing with domain elements, which cannot be in
        // quantifiers, we do not need to worry about variable capture in
        // substitution and can use the faster substituter.
        val newAxioms = theory.axioms.map(axiom => axiom.eliminateEnumValues(mapping))
        
        val newSignature = theory.signature.withoutEnums
        
        Theory.mkTheoryWithSignature(newSignature)
            .withScopes(theory.scopes)
            .withAxioms(newAxioms)
    }
    
    def computeEnumSortMapping(theory: Theory): Map[EnumValue, DomainElement] = {
        val mapping = scala.collection.mutable.Map[EnumValue, DomainElement]()
        for((sort, enumConstants) <- theory.enumConstants) {
            enumConstants.zipWithIndex.foreach { case (constant, index) =>
                mapping += constant -> DomainElement(index + 1, sort)
            }
        }
        mapping.toMap
    }
    
    override def name: String = "Enum Elimination Transformer"
}
