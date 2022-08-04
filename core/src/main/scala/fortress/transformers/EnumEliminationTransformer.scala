package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.interpretation.Interpretation

/** Replaces enum values with domain elements, following the mapping from the
  * computeEnumSortMapping method.
  */
object EnumEliminationTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val mapping = computeEnumSortMapping(theory)
            
            // Since we are replacing with domain elements, which cannot be in
            // quantifiers, we do not need to worry about variable capture in
            // substitution and can use the faster substituter.
            val newAxioms = theory.axioms.map(_.eliminateEnumValues(mapping))
            
            val newSignature = theory.signature.withoutEnums
            
            val newTheory = Theory.mkTheoryWithSignature(newSignature)
                .withAxioms(newAxioms)
            
            val unapply: Interpretation => Interpretation = _.replaceValuesWithEnums(mapping.map(_.swap))

//            println("Theory after enum elimination transformer :\n")
//            println(newTheory + "\n---------------------------------\n")
            
            // The problem contain scopes for the enums, which should remain the same
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapply :: unapplyInterp, distinctConstants)
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
