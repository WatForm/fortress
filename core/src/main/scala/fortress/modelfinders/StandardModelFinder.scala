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
import scala.collection.mutable.ListBuffer

/**

  Definitions for model finders functions

  Note: this class can't have arguments if we want to use a straightforward string
  registry to look it up!

  See ConfigurableModelFinder to use and API interface that takes classes for the compiler,solver
  as arguments.

  */
class StandardModelFinder extends ModelFinder {

    protected var theory: Theory = Theory.empty
    // good defaults for compiler and solver 
    protected var compiler:Compiler = new StandardCompiler
    protected var solver:Solver = new Z3NonIncCliSolver

    // can be set by user (see functions below)
    protected var timeoutMilliseconds: Milliseconds = Milliseconds(60000)
    protected var analysisScopes: Map[Sort,Scope] = Map.empty

    // internal variables
    protected var eventLoggers: ListBuffer[EventLogger] = ListBuffer.empty
    // Counts the total time elapsed
    private val totalTimer: StopWatch = new StopWatch()
    private var compilerResult: Option[CompilerResult] = None


    /** Set the theory of the model finder. */
    def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    def setSolver(newSolver: Solver): Unit = {
        solver = newSolver
    }
    def setSolver(newSolver: String): Unit = {
        // exception raised if solver does not exist
        solver = SolversRegistry.fromString(newSolver)
    }
    def setCompiler(newCompiler: Compiler): Unit = {
        compiler = newCompiler
    }    
     def setCompiler(newCompiler: String): Unit = {
        // exception raised if compiler does not exist
        compiler = CompilersRegistry.fromString(newCompiler)

    }    

    /** Set the timeout in milliseconds. */
    def setTimeout(milliseconds: Milliseconds): Unit = {
        Errors.Internal.precondition(milliseconds >= Milliseconds(0))
        timeoutMilliseconds = milliseconds
    }

    /** Set the timeout in seconds. */
    def setTimeout(seconds: Seconds): Unit = {
        setTimeout(seconds.toMilli)
    }

    /** Set the exact scope of the given sort, which is the size of the domain for that sort. */
    def setScope(sort: Sort, scope: Scope): Unit = {
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        Errors.Internal.precondition(scope.size>0)
        analysisScopes = analysisScopes + (sort -> scope)
    }

    /** |A| = 3 **/
    def setExactScope(sort: Sort, size: Int): Unit = {
        Errors.Internal.precondition(size > 0)
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        // note that IntSort scopes are specified in bitwidth
        val scope = ExactScope(size)
        analysisScopes = analysisScopes + (sort -> scope)
    }

    /** Set the non-exact scope of the given sort, which is the size of the domain for that sort. */
    /** |A| <= 3 **/
    def setNonExactScope(sort: Sort, size: Int): Unit = {
        Errors.Internal.precondition(size > 0)
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        // note that IntSort scopes are specified in bitwidth
        val scope = NonExactScope(size)
        analysisScopes = analysisScopes + (sort -> scope)
    }

    def setOutput(writer: java.io.Writer): Unit = {
        eventLoggers += new StandardLogger(writer)
    }
    
    def addLogger(logger: EventLogger): Unit = {
        eventLoggers += logger
    }
    
    // Calculate the number of nanoseconds until we must output TIMEOUT
    protected def timeoutNano: Nanoseconds = timeoutMilliseconds.toNano
    
    protected def notifyLoggers(notifyFn: EventLogger => Unit): Unit = 
        for(logger <- eventLoggers) notifyFn(logger)

    def compile(verbose: Boolean = false): Either[CompilerError, CompilerResult] = {
        compiler.compile(theory, analysisScopes, timeoutMilliseconds, eventLoggers.toList, verbose) 
    }

    /** Check for a satisfying interpretation to the theory with the given scopes. */
    def checkSat(verbose: Boolean = false): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()

        //compiler = Some(createCompiler())

        this.compile(verbose) match {
            case Left(CompilerError.Timeout) => TimeoutResult
            case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
            case Right(compilerRes) => {
                compilerResult = Some(compilerRes)

                val finalTheory = compilerResult.get.theory

//                println("final theory: \n" + finalTheory + "\n\n")

                notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano))

                val finalResult: ModelFinderResult = solverPhase(finalTheory)

                finalResult
            }
        }
    }

    // Returns the final ModelFinderResult
    private def solverPhase(finalTheory: Theory): ModelFinderResult = {
        notifyLoggers(_.invokingSolverStrategy())
        
        // Close solver session, if one has already been started
        solver.close()
        
        // Open new solver session
        //val session = solverInterface.openSession()
        //solverSession = Some(session)

        // Convert to solver format
        notifyLoggers(_.convertingToSolverFormat())
        val (_, elapsedConvertNano) = measureTime[Unit] {
            solver.setTheory(finalTheory)
        }
        notifyLoggers(_.convertedToSolverFormat(elapsedConvertNano))

        // Solve
        val (finalResult, elapsedSolverNano) = measureTime {
            val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
            solver.solve(remainingMillis)
        }
        notifyLoggers(_.solverFinished(elapsedSolverNano))

        notifyLoggers(_.finished(finalResult, totalTimer.elapsedNano()))

        finalResult
    }

    /** View the satisfying interpretation, if one exists.
      * Otherwise, throws an error.
      * Can only be called after checkSat.
      */
    def viewModel(): Interpretation = {
        val instance = solver.solution
        compilerResult.get.decompileInterpretation(instance)
    }

    /** Return the next satisfying interpretation. */
    def nextInterpretation(): ModelFinderResult = {
        // Negate the current interpretation, but leave out the skolem functions
        // Different witnesses are not useful for counting interpretations
        val instance = solver.solution
            .withoutDeclarations(compilerResult.get.skipForNextInterpretation)

        val newInstance: Interpretation = {

            def scopes: Map[Sort, Int] = for((sort, seq) <- instance.sortInterpretations) yield (sort -> seq.size)

            val newFunctionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = {
                for(f <- theory.signature.functionDeclarations)
                    yield f -> {
                        for (argList <- ArgumentListGenerator.generate(f, scopes, Some(instance.sortInterpretations)))
                            yield argList -> instance.getFunctionValue(f.name, argList)
                        }.toMap

            }.toMap

            new BasicInterpretation(
                instance.sortInterpretations,
                instance.constantInterpretations,
                newFunctionInterpretations,
                instance.functionDefinitions
            )
        }

//        println("instance:\n " + newInstance)

        val newAxiom = Not(And.smart(newInstance.toConstraints.toList map (compilerResult.get.eliminateDomainElements(_))))

//        println("newAxiom: " + newAxiom)

        solver.addAxiom(newAxiom)
        solver.solve(timeoutMilliseconds)
    }



    /** Count the total number of satisfying interpretations. */

    def countValidModels(newTheory: Theory): Int = {
        theory = newTheory

        // deleting this precondition is because those theory with enum sort
//        Errors.Internal.precondition(theory.signature.sorts.size == analysisScopes.size,
//            "Sorry, we can't count valid models for a theory with unbounded sorts")
        
        checkSat() match {
            case SatResult =>
            case UnsatResult => return 0
            case UnknownResult => Errors.Internal.solverError("Solver gave unknown result")
            case ErrorResult(_) => Errors.Internal.solverError("An error occurred while computing result")
            case TimeoutResult => Errors.Internal.solverError("Solver timed out while computing result")
        }

        var count: Int = 1

        var sat: Boolean = true
        while (sat) {

            val result = nextInterpretation()

            result match {
                case SatResult => count += 1
                case UnsatResult => sat = false
                case UnknownResult => Errors.Internal.solverError("Solver gave unknown result")
                case ErrorResult(_) => Errors.Internal.solverError("An error occurred while computing result")
                case TimeoutResult => Errors.Internal.solverError("Solver timed out while computing result")
            }

        }
        // Returning count
        count
    }

    // Count the Valid Models in the current theory
    def countValidModels(): Int = countValidModels(theory)

    
    
    @throws(classOf[java.io.IOException])
    def close(): Unit = {
        solver.close()
    }

}





