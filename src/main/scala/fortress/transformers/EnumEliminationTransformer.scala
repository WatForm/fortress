package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._

/** Replaces enum values with domain elements, following the mapping from the
  * computeEnumSortMapping method. */
class EnumEliminationTransformer extends ProblemTransformer {
    override def apply(problem: Problem): Problem = problem match {
        case Problem(theory, scopes) => {
            val mapping = computeEnumSortMapping(theory)
            
            // Since we are replacing with domain elements, which cannot be in
            // quantifiers, we do not need to worry about variable capture in
            // substitution and can use the faster substituter.
            val newAxioms = theory.axioms.map(_.eliminateEnumValues(mapping))
            
            val newSignature = theory.signature.withoutEnums
            
            val newTheory = Theory.mkTheoryWithSignature(newSignature)
                .withAxioms(newAxioms)
            
            // The problem contain scopes for the enums, which should remain the same
            Problem(newTheory, scopes)
        }
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
