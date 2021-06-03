package fortress.transformers

import fortress.msfol._
import fortress.util.Errors
import fortress.interpretation.Interpretation

/**
  * Contains a theory, scopes, and additional information that is used throughout the transformation process.
  *
  * @param theory the theory
  * @param scopes the scopes for the theory
  * @param skolemConstants introduced skolem constants
  * @param skolemFunctions introduced skolem functions
  * @param rangeRestrictions introduced range restrictions (these also exist as formulas within the theory)
  * @param unapplyInterp a LIFO stack of instructions (given as a LIFO stack of functions) that describe how to undo 
  *                      the transformations thus far when giving an interpretation back to the user 
  */
case class ProblemState private(
    theory: Theory,
    scopes: Map[Sort, Int],
    skolemConstants: Set[AnnotatedVar],
    skolemFunctions: Set[FuncDecl],
    rangeRestrictions: Set[RangeRestriction],
    unapplyInterp: List[Interpretation => Interpretation]
) {
    Errors.Internal.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.Internal.precondition(scopes.keySet.forall(!_.isBuiltin))
    // All scoped sorts are within the theory
    Errors.Internal.precondition(scopes.keySet subsetOf theory.sorts)
    
    // TODO add precondition that theory domain elements respect the scopes
}

object ProblemState {
    def apply(theory: Theory): ProblemState = ProblemState(theory, Map.empty)
    
    def apply(theory: Theory, scopes: Map[Sort, Int]): ProblemState = {
        // Compute the scopes for enum sorts
        val enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap

        // Check there is no conflict between the enum scopes and the provided scopes
        Errors.Internal.precondition(fortress.util.Maps.noConflict(enumScopes, scopes))

        new ProblemState(
            theory,
            scopes ++ enumScopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty
        )
    }
}
