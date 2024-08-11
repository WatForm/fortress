package fortress.compilers

import fortress.msfol.{Declaration, Term, Theory}
import fortress.interpretation.Interpretation
import fortress.problemstate.TrivialResult

/** Result from a compiler. */
trait CompilerResult {

    /** The output theory from the compilation process. */
    val theory: Theory

    /** Set if the compilation process determines that the theory is trivially sat or unsat. */
    val trivialResult: Option[TrivialResult]
    def isTrivial: Boolean = trivialResult.isDefined

    /**
      * A function which undoes the transformations in the compilation process for an interpretation.
      */
    def decompileInterpretation(interpretation: Interpretation): Interpretation

    /**
      * A list of auxiliary functions generated during the compilation process which should be ignored
      * when negating interpretations (for example, skolem functions). 
      */
    val skipForNextInterpretation: Set[Declaration]

    /**
      * A function which eliminates domain elements in a term based on either distinct constants
      * or datatype method.
      */
    def eliminateDomainElements(term: Term): Term
}

sealed trait CompilerError

object CompilerError {
    case object Timeout extends CompilerError
    case class Other(message: String) extends CompilerError
}