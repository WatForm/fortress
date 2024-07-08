package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.logging._
import fortress.operations.TermOps._
import fortress.problemstate._
import fortress.util.Control.measureTime
import fortress.util.Control.withCountdown
import fortress.util.Extensions._

/**
  * Converts a theory with scopes into another ``lower-level" theory, intended to be sent to an external solver.
  * Performs this process through a sequence of transformations.
  */
abstract class Compiler {

   def transformerSequence: Seq[ProblemStateTransformer]
        
   def compile(
        theory: Theory,
        scopes: Map[Sort, Scope],
        timeout: Milliseconds,
        loggers: Seq[EventLogger],
        verbose: Boolean,
    ): Either[CompilerError, CompilerResult]

   // do not overwrite in a subclass
   def name = StringHelpers.chopOff(this.getClass.getSimpleName,"Compiler")
}

/**
  * For debugging purposes, interleaves type-checking after each step of the parent compiler's transformers.
  * This should not be done in production code, since it will slow things down.
  */
trait PervasiveTypeChecking extends Compiler {
    abstract override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformers = super.transformerSequence.toList
        val n = transformers.length
        val typecheckers: List[ProblemStateTransformer] = for(i <- (1 to n).toList) yield TypecheckSanitizeTransformer
        transformers interleave typecheckers
    }
}