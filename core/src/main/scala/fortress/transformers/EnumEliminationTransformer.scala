package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.interpretation.Interpretation
import fortress.problemstate.ProblemState
import fortress.problemstate.ExactScope

/** Replaces enum values with domain elements, following the mapping from the
  * computeEnumSortMapping method.
  */
object EnumEliminationTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        
        val mapping = computeEnumSortMapping(theory)
        
        // Since we are replacing with domain elements, which cannot be in
        // quantifiers, we do not need to worry about variable capture in
        // substitution and can use the faster substituter.
        val newAxioms = theory.axioms.map(_.eliminateEnumValues(mapping))
        
        var newSig = theory.signature
                        .withoutEnums
        
        // Replace scopes of enums with exact scope
        var newScopes = problemState.scopes

        for ((sort, enumConstants) <- theory.enumConstants) {
            newScopes = newScopes.updated(sort, ExactScope(enumConstants.length, true))
        }

        // We only remove a definition before readding it so all its dependencies are in the sig
        // definitions are basically untested
        for(cDef <- theory.signature.constantDefinitions){
            newSig = newSig.withoutConstantDefinition(cDef)
            newSig = newSig.withConstantDefinition(cDef.mapBody(_.eliminateEnumValues(mapping)))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newSig = newSig.withoutFunctionDefinition(fDef)
            newSig = newSig.withFunctionDefinition(fDef.mapBody(_.eliminateEnumValues(mapping)))
        }
        
        val newTheory = Theory(newSig, newAxioms)
        
        val unapply: Interpretation => Interpretation = _.replaceValuesWithEnums(mapping.map(_.swap))

        // The problem contain scopes for the enums, which should remain the same
        //ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapply :: unapplyInterp, distinctConstants)
        problemState.copy(
            theory = newTheory,
            unapplyInterp = unapply :: problemState.unapplyInterp,
            scopes = newScopes
        )
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
    

}
