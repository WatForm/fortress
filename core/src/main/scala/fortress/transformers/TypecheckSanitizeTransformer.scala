package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._
import fortress.util.Errors

import scala.collection.mutable

/** Type-checks a theory, and performs sanitization (for example, replacing Equals of booleans with Iff).
  * Throws an exception if the theory does not type-check correctly.
  */
object TypecheckSanitizeTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            // change illegal names by adding prefix "aa" and suffix "aa"
            val affix = "aa"
            val renameMap: mutable.Map[String, String] = mutable.Map.empty
            var newTheory = IllegalNameSubstitution(affix).apply(theory, renameMap)

            def sanitizeAxiom(axiom: Term): Term = {
                // Check axiom typechecks as bool
                // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
                val result: TypeCheckResult = axiom.typeCheck(newTheory.signature)
                // System.out.println(axiom.toString + (result.sort).toString) ;
                Errors.Internal.precondition(result.sort == BoolSort)
                result.sanitizedTerm
            }

            newTheory = newTheory.mapAxioms(t => sanitizeAxiom(t))

            val unapply: Interpretation => Interpretation = _.applyNameSubstitution(renameMap.toMap)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapply :: unapplyInterp)
        }
    }

    override def name: String = "Typecheck & Sanitize Transformer"
}