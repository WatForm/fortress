package fortress.compiler

import fortress.msfol.Theory
import fortress.interpretation.Interpretation
import fortress.msfol.Declaration

/** Result from a compiler. */
trait CompilerResult {

    /** The output theory from the compilation process. */
    val theory: Theory

    /**
      * A function which undoes the transformations in the compilation process for an interpretation.
      */
    def decompileInterpretation(interpretation: Interpretation): Interpretation

    /**
      * A list of auxiliary functions generated during the compilation process which should be ignored
      * when negating interpretations (for example, skolem functions). 
      */
    val skipForNextInterpretation: Set[Declaration]
}

sealed trait CompilerError

object CompilerError {
    case object Timeout extends CompilerError
    case class Other(message: String) extends CompilerError
}