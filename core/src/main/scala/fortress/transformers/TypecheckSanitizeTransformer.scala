package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._
import fortress.util.Errors

/** Type-checks a theory, and performs sanitization (for example, replacing Equals of booleans with Iff).
  * Throws an exception if the theory does not type-check correctly.
  */
object TypecheckSanitizeTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {

        def sanitizeAxiom(axiom: Term): Term = {
            // Check axiom typechecks as bool
            // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
            val result: TypeCheckResult = axiom.typeCheck(theory.signature)
            // System.out.println(axiom.toString + (result.sort).toString) ;
            Errors.Internal.precondition(result.sort == BoolSort)
            result.sanitizedTerm
        }

        theory.mapAxioms(t => sanitizeAxiom(t))
    }
    
    override def name: String = "Typecheck & Sanitize Transformer"
}