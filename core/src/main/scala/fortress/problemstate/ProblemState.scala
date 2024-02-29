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
  * @param distinctConstants ?
  * @param isNNF flag set to true to indicate every formula is in negation normal form
  * @param verbose flag set to indicate output should be verobse
  */
case class ProblemState private(
    theory: Theory,
    scopes: Map[Sort, Scope],
    skolemConstants: Set[AnnotatedVar],
    skolemFunctions: Set[FuncDecl],
    rangeRestrictions: Set[RangeRestriction],
    unapplyInterp: List[Interpretation => Interpretation],
    flags: Flags
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
        copy(theory = newtheory)
    }
    def withScopes(newscopes: Map[Sort, Scope]): ProblemState = {
        val unchangingScopeSorts = scopes.filter((scopeInfo: (Sort, Scope)) => scopeInfo._2.isUnchanging)
        // Check that every unchanging scope is unchanged
        Errors.Internal.precondition(unchangingScopeSorts.forall((scopeInfo: (Sort, Scope)) => newscopes.get(scopeInfo._1) == Some(scopeInfo._2)), "Attempted to change an unchanging scope!")
        copy(scopes = newscopes)
        
    }

    def withUnapplyInterp(unapp: Interpretation => Interpretation): ProblemState = {
        copy(unapplyInterp = unapplyInterp :+ unapp)
    }

    def withoutUnapplyInterps(): ProblemState = {
        copy(unapplyInterp = List.empty)
    }
}

object ProblemState {

    def apply(theory: Theory): ProblemState = ProblemState(theory, Map.empty)
    
    def apply(theory: Theory, scopes: Map[Sort, Scope], verbose: Boolean = false): ProblemState = {
        // Compute the scopes for enum sorts
        // Copy whether the scope is fixed and its exactness from the regular scope if applicable for compatibility
        def isFixed(sort: Sort) =
            if (scopes contains sort) scopes(sort).isUnchanging
            else true
        def makeScopeWithExactness(sort: Sort, size: Int, isUnchanging: Boolean) =
            if ((scopes contains sort) && scopes(sort).isExact) ExactScope(size, isUnchanging)
            else NonExactScope(size, isUnchanging)
        val enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> makeScopeWithExactness(sort, enumValues.size, isFixed(sort))
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
            flags = Flags(verbose=verbose)
        )
    }


}
