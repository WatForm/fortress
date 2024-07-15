// Go through iflifting

package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState


/** Changes each axiom of the theory into negation normal form. */
object IfLiftingTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {

        //if (problemState.flags.containsItes) {

            val theory = problemState.theory

            // axioms are of Boolean type so we can remove all ites from them
            // remember we can't necessarilly do iflifting on everything, just boolean types
            // for axioms we knonw they are boolean types already so we don't have to do any preprocessing before iflifting
            // I'm assuming t.iflift calls the iflift operation
            var newTheory = theory.mapAxioms(t => t.iflift(BoolSort))

            // iflifting for defns can be done
            // but may not remove all ites
            // if the return sort of the defn body is not Boolean

            for(cDef <- theory.signature.constantDefinitions){
                // removing and replacing a constant definition, just now mapped
                // take our the constant
                // ifLift it
                // put it back in
                newTheory = newTheory.withoutConstantDefinition(cDef)
                newTheory = newTheory.withConstantDefinition(cDef.mapBody(t => t.iflift(cDef.sort)))
            }
            for(fDef <- theory.signature.functionDefinitions){
                // same idea with function defs
                // remove function def from theory
                // iflift it
                // put it back in
                newTheory = newTheory.withoutFunctionDefinition(fDef)
                newTheory = newTheory.withFunctionDefinition(fDef.mapBody(t => t.iflift(fDef.resultSort)))
            }

            return problemState.copy(
                theory = newTheory,
                flags = problemState.flags.copy(
                    haveRunIfLifting = true
                )
            )

        // so at this point have we removed all of the iflifting? or just all the iflifting we can???
        /*
        } else {
            return problemState
        }
        */
    }


}
