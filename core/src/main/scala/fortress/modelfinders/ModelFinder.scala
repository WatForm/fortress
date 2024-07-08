/*
 * This class shows the API interface for a model finder 
   to search for satisfying models to theories with scopes.
   Extends AutoCloseable because it may hold a resource, such as an open connection to an SMT solver, which must be closed.

  The three most important settings of a Model Finder are:
  setTheory
  setCompiler 
  setSolver
  There are good defaults chosen for the compiler and the solver, but nothing will happen if a theory is not set.

  There are other settings such as timeouts and scopes of sorts.
  
 */

package fortress.modelfinders

import fortress.util._
import fortress.util.Control.measureTime
import fortress.msfol._
import fortress.interpretation._
import fortress.compilers._
import fortress.solvers._
import fortress.logging._
import fortress.problemstate._

import java.lang.AutoCloseable
import java.lang.Class
import scala.collection.mutable.ListBuffer

abstract class ModelFinder extends AutoCloseable {


   def setTheory(newTheory: Theory): Unit 

   def setSolver(newSolver: Solver): Unit
   def setSolver(newSolver: String): Unit

   def setCompiler(newCompiler: Compiler): Unit
   def setCompiler(newCompiler: String): Unit

   def setTimeout(milliseconds: Milliseconds): Unit
   def setTimeout(seconds: Seconds): Unit
   def setScope(sort: Sort, scope: Scope): Unit
   def setExactScope(sort: Sort, size: Int): Unit
   def setNonExactScope(sort: Sort, size: Int): Unit
   def setOutput(writer: java.io.Writer): Unit

   def addLogger(logger: EventLogger): Unit

   // operations
   def compile(verbose: Boolean = false): Either[CompilerError, CompilerResult]
   def checkSat(verbose: Boolean = false): ModelFinderResult
   def viewModel(): Interpretation
   def nextInterpretation(): ModelFinderResult
   def countValidModels(): Int
   def countValidModels(newTheory: Theory): Int

   // closes the solvers 
   def close(): Unit

   // do not overwrite in a subclass
   def name = StringHelpers.chopOff(this.getClass.getSimpleName,"ModelFinder")

}
