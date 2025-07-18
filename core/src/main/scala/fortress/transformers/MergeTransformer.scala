/**
  * A transformer that takes two related theories and sets up
  * a final theory that is the result of merging and semantically
  * comparing them:
  * the resulting theory is satisfiable if the instances
  * statisfies the first theory but not the second theory.
  */

package fortress.transformers

import fortress.operations.EvaluationInliner
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/* these are all elements of a problemState:
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

class MergeTransformer (
    secondProblemState: ProblemState
) extends ProblemStateTransformer {

    override def apply(firstProblemState: ProblemState): ProblemState = {
        var theory1 = firstProblemState.theory
        var theory2 = secondProblemState.theory
/*
        // sorts and scopes: merge sets of sorts
        // checking scopes are the same 
        val theory1sortNames = theory1.signature.sorts.map(_.name)
        val theory2sortNames = theory2.signature.sorts.map(_.name)
        for s2 <- theory2sortNames {
          if theory1sortNames contains s2 then
            if firstProblemState.scopes(s2).size != secondProblemState.scopes(s2).size then 
              throw Errors.API.preconditionFailed("problemStates are not disjoint for MergeTransformer")
            end if
          end if
          newSorts = theory1.signature.sorts ++ theory2.signature.sorts
          // since we've already determined that scopes are consistent
          // between the two sets of scopes, just merge them
          newScopes = firstProblemState.scopes ++ secondProblemState.scopes 
        }

        // declarations: if same name, must have same sort expression
        val theory1constantDeclsNames = theory1.signature.constantDeclarations.map(_.name)
        val theory2constantDeclsNames = theory2.signature.constantDeclarations.map(_.name)
        for s2 <- theory2constantDeclsNames {
          if theory1constantDeclsNames contains s2 then
            if theory1.constantDeclarations(s2).sort != theory2.constantDeclarations(s2).sort then 
              throw Errors.API.preconditionFailed("problemStates are not disjoint for MergeTransformer")
            end if
          end if
          newConstantDeclarations = theory1.signature.constantDeclarations ++ theory2.signature.constantDeclarations
          // since we've already determined that scopes are consistent
          // between the two sets of scopes, just merge them
          newScopes = firstProblemState.scopes ++ secondProblemState.scopes 
        }




        // definitions: if same name, must be same body or else error
        // axioms:
        // from theory1, just add all of its axioms (this means the conjunction of all of its axioms)
        // from theory2, create one disjunction of the negation of each axiom 
        val newAxioms = theory.axioms.map(inliner.naturalRecur)
        

        // this will have to create a new theory
        // scopes should be the same between the two
        // what do we do about scopes? 
        // for the same sorts, must have the same scopes
        problemState
        .withTheory(newTheory)
        .withFlags(problemState.flags.copy(trivialResult = newTheory.checkTrivial))
*/
      firstProblemState
    }
}