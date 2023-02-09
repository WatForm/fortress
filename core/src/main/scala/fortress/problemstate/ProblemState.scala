package fortress.problemstate

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.util.Errors

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
    scopes: Map[Sort, Scope],
    skolemConstants: Set[AnnotatedVar],
    skolemFunctions: Set[FuncDecl],
    rangeRestrictions: Set[RangeRestriction],
    unapplyInterp: List[Interpretation => Interpretation],
    distinctConstants: Boolean
) {
//    Errors.Internal.precondition(scopes.values.forall(_. > 0), "Scopes must be positive")
    // allow setting scope for IntSort but not other builtins
    // Errors.Internal.precondition(scopes.keySet.forall( (x:Sort) => !x.isBuiltin || x == IntSort))
    // All scoped sorts are within the theory or IntSort
    // Errors.Internal.precondition(scopes.keySet subsetOf theory.sorts + IntSort)

    // All bitvectors are properly sized
    Errors.Internal.precondition(scopes.keySet.forall( (x:Sort) => x match {
        case BitVectorSort(bitwidth) => scopes(x).size == math.pow(2, bitwidth).toInt
        case _ => true
    }),
    "Bitvector has incorrect size")
    
    // TODO add precondition that theory domain elements respect the scopes

    def withTheory(newtheory: Theory): ProblemState = {
        new ProblemState(            
            newtheory,    // replaces just the theory
            scopes,
            skolemConstants,
            skolemFunctions,
            rangeRestrictions,
            unapplyInterp,
            distinctConstants)
    }
    def withScopes(newscopes: Map[Sort, Scope]): ProblemState = {
        val unchangingScopeSorts = scopes.filter((scopeInfo: (Sort, Scope)) => scopeInfo._2.isUnchanging)
        // Check that every unchanging scope is unchanged
        Errors.Internal.precondition(unchangingScopeSorts.forall((scopeInfo: (Sort, Scope)) => newscopes.get(scopeInfo._1) == Some(scopeInfo._2)), "Attempted to change an unchanging scope!")
        new ProblemState(            
            theory,    
            newscopes, // replaces just the scopes
            skolemConstants,
            skolemFunctions,
            rangeRestrictions,
            unapplyInterp,
            distinctConstants)
    }
}

object ProblemState {

    def apply(theory: Theory): ProblemState = ProblemState(theory, Map.empty)
    
    def apply(theory: Theory, scopes: Map[Sort, Scope]): ProblemState = {
        // Compute the scopes for enum sorts
        // Copy whether the scope is fixed from the regular scope if applicable for compatibility
        def isFixed(sort: Sort) =
            if (scopes contains sort) scopes(sort).isUnchanging
            else true
        val enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> ExactScope(enumValues.size, isFixed(sort))
        }.toMap

        // Check there is no conflict between the enum scopes and the provided scopes
        Errors.Internal.precondition(fortress.util.Maps.noConflict(enumScopes, scopes), "Conflict between enums and provide scopes")

        new ProblemState(
            theory,
            scopes ++ enumScopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty,
            distinctConstants = true
        )
    }


}
