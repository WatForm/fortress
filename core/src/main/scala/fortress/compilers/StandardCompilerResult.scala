package fortress.compilers

import fortress.msfol._
import fortress.util._
import fortress.interpretation._
import fortress.operations.TermOps._
import fortress.problemstate._




/** implementation of CompilerResult */

class StandardCompilerResult(val finalProblemState: ProblemState) extends CompilerResult {

    val theory: Theory = finalProblemState.theory

    val trivialResult: Option[TrivialResult] = finalProblemState.flags.trivialResult

    def decompileInterpretation(interpretation: Interpretation): Interpretation = {
        finalProblemState.unapplyInterp.foldLeft(interpretation) {
            (interp, unapplyFn) => unapplyFn(interp)
        }
    }

    val skipForNextInterpretation: Set[Declaration] = {
        // We have to use some type hackery to get around the invariance of Set[A]
        (finalProblemState.skolemConstants.map(x => x: Declaration)) union finalProblemState.skolemFunctions.map(x => x: Declaration)
    }

    override def eliminateDomainElements(term: Term): Term = {
        if (finalProblemState.flags.distinctConstants) {
            term.eliminateDomainElementsConstants
        } else {
            term.eliminateDomainElementsEnums
        }
    }
}