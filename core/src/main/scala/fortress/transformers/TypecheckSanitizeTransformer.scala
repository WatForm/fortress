package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._
import fortress.util.Errors

class TypecheckSanitizeTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory = {

        def sanitizeAxiom(axiom: Term): Term = {
            // Check axiom typechecks as bool
            // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
            val result: TypeCheckResult = axiom.typeCheck(theory.signature)
            // System.out.println(axiom.toString + (result.sort).toString) ;
            Errors.precondition(result.sort == BoolSort)
            result.sanitizedTerm
        }

        theory.mapAxioms(t => sanitizeAxiom(t))
    }
    
    override def name: String = "Typecheck & Sanitize Transformer"
}