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
    
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        var containsItes = false
        var containsExists = false
        def sanitizeAxiom(axiom: Term): Term = {
            // Check axiom typechecks as bool
            // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
            val result: TypeCheckResult = axiom.typeCheck(theory.signature)
            containsItes = containsItes || result.containsItes
            containsExists = containsExists || result.containsExists
            // System.out.println(axiom.toString + (result.sort).toString) ;
            Errors.Internal.precondition(result.sort == BoolSort)
            result.sanitizedTerm
        }

        val newTheory = theory.mapAxioms(t => sanitizeAxiom(t))

        // somehow we need to get the ite/exists results from all t's aggregrated

        problemState.copy(
            theory = newTheory,
            flags = problemState.flags.copy(
                containsItes = containsItes,
                containsExists = containsExists
            )
        )
    }
    
    override def name: String = "Typecheck & Sanitize Transformer"
}