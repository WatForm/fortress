package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._
import fortress.util.Errors
import fortress.problemstate.ProblemState

/** Type-checks a theory, and performs sanitization (for example, replacing Equals of booleans with Iff).
  * Throws an exception if the theory does not type-check correctly.
  */
object TypecheckSanitizeTransformer extends ProblemStateTransformer {

    // Note that a formula will not typecheck if it has any free variables (that are not constants of the signature)

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        var containsItes = false
        var containsExists = false
        var contains2ndOrder = false

        def checkResult(result: TypeCheckResult, s: Sort): Term = {
            containsItes = containsItes || result.containsItes
            containsExists = containsExists || result.containsExists
            contains2ndOrder = contains2ndOrder || result.containsQuantifiers2ndOrder
            // System.out.println(axiom.toString + (result.sort).toString) ;
            if (result.sort != s) 
                // This error message isn't great because typechecking does change
                // some parts of the term such as ites over Booleans
                Errors.Internal.preconditionFailed(s"typechecking of "+result.sanitizedTerm.toString + " had sort "+ result.sort.toString + "when it should be "+s)
            return result.sanitizedTerm            
        }        
        var newTheory = theory.mapAxioms(
                t => checkResult(t.typeCheck(theory.signature), BoolSort))

        // There is nothing to stop recursive definitions
        for(cDef <- theory.signature.constantDefinitions){
            newTheory = newTheory.withoutConstantDefinition(cDef)
            newTheory = newTheory.withConstantDefinition(
                cDef.mapBody(b => 
                    checkResult(cDef.body.typeCheck(theory.signature),cDef.sort)))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newTheory = newTheory.withoutFunctionDefinition(fDef)
            newTheory = newTheory.withFunctionDefinition(
                fDef.mapBody(b => 
                    checkResult(
                        fDef.body.typeCheckInContext(theory.signature,fDef.argSortedVar),
                        fDef.resultSort)))
        }

        problemState
        .withTheory(newTheory)
        .withFlags(
            problemState.flags.copy(
                containsItes = containsItes,
                containsExists = containsExists,
                constains2ndOrderQuantifiers = contains2ndOrder
            )
        )
    }
    

}