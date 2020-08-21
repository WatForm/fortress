package fortress.compiler

import fortress.msfol._
import fortress.interpretation._
import fortress.util._
import fortress.logging._

trait LogicCompiler {
    def compile(
        theory: Theory,
        scopes: Map[Sort, Int],
        timeout: Milliseconds,
        loggers: Seq[EventLogger]
    ): Either[CompilerError, CompilerResult]
}

trait CompilerResult {
    def theory: Theory

    def decompileInterpretation(interpretation: Interpretation): Interpretation

    def skipForNextInterpretation: Set[Declaration]
}

sealed trait CompilerError
case object Timeout extends CompilerError
case class Other(message: String) extends CompilerError