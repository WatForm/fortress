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
  * @param flags set to if a transformer has been run
  * @param verbose flag set to indicate output should be verobse
  */

// private here means no one can write new ProblemState elsewhere in the code
// class ProblemState is only visible to itself and its companion object
// the real constructors for this are in the companion object below

class ProblemState (
    theory: Theory,
    scopes: Map[Sort, Scope],
    verbose: Boolean = false,
    correctnessChecks: Boolean = false
) {

    private var skolemConstants: Set[AnnotatedVar] = Set.empty
    private var skolemFunctions: Set[FuncDecl] = Set.empty
    private var rangeRestrictions: Set[RangeRestriction] = Set.empty
    private var unapplyInterp: List[Interpretation => Interpretation] = List.empty

    // 'state' flags
    private var isPartialNNF: Boolean = false
    private var usesDistintConstantsForDEs: Boolean = false
    private var containsItes: Boolean = false,  
    private var containsExists: Boolean = false,
    private var containtsQuantifiers: Boolean = false

    // 'process' flags
    // these are set by an individual transformer
    // and cause warnings to be issued if a transformer has not
    // been run before another
    private var haveRunIfLifting: Boolean = false
    private var haveRunNnf: Boolean = false
    private var haveRunSkolemizer: Boolean = false,

    // initialization
    // ???
    // should we run typechecking right away???

    // make sure any sorts in the scope map are sorts in the theory



    // Compute the scopes for enum sorts
    // Copy whether the scope is fixed and its exactness from the regular scope if applicable for compatibility

    val enumScopes = theory.signature.enumConstants.map {
        case (sort, enumValues) => sort -> makeScopeWithExactness(sort, enumValues.size, isFixed(sort))
    }.toMap

    flags.containsNonExactScopes = scopes.values.exists(sc => sc.isExact == false)
    // Check there is no conflict between the enum scopes and the provided scopes
    Errors.Internal.precondition(fortress.util.Maps.noConflict(enumScopes, scopes), "Conflict between enums and provide scopes")

    def isFixed(sort: Sort) =
        if (scopes contains sort) scopes(sort).isUnchanging
        else true


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
        theory = newtheory
    }
    def withScopes(newscopes: Map[Sort, Scope]): ProblemState = {
        scopes = newscopes
        /*
        val unchangingScopeSorts = scopes.filter((scopeInfo: (Sort, Scope)) => scopeInfo._2.isUnchanging)
        // Check that every unchanging scope is unchanged
        Errors.Internal.precondition(unchangingScopeSorts.forall((scopeInfo: (Sort, Scope)) => newscopes.get(scopeInfo._1) == Some(scopeInfo._2)), "Attempted to change an unchanging scope!")
        copy(scopes = newscopes)
        */
    }

    def withUnapplyInterp(unapp: Interpretation => Interpretation): ProblemState = {
        copy(unapplyInterp = unapplyInterp :+ unapp)
    }

    def withoutUnapplyInterps(): ProblemState = {
        copy(unapplyInterp = List.empty)
    }

    def withFlags(fl:Flags):ProblemState = {
        copy(flags = fl)
    }
}

object ProblemState {

    // this is the only actually the constructors of ProblemStates b/c above is private
    // so default field values do not need to be set above because the first constructor 
    // calls the second constructor, which gives values to all the fields

    // putting the type on Map.empty is needed here so that it knows whether
    // to call the second or third constructor here
       
    def apply(theory: Theory, scopes: Map[Sort, Scope], verbose: Boolean = false): ProblemState = {

        new ProblemState(
            theory,
            scopes ++ enumScopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty,
            flags = Flags(verbose=verbose, containsNonExactScopes=containsNonExactScopes)
        )
    }

}
