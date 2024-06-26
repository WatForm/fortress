package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._
import fortress.compiler._
import fortress.logging._
import fortress.msfol.DSL.DSLTerm
import fortress.util.Control.measureTime

/** Model finder which invokes a compiler to reduce the model finding problem to satisfiability over a simpler logic. */
abstract class CompilationModelFinder(solverInterface: SolverInterface)
extends ModelFinder
with ModelFinderSettings {

    // Counts the total time elapsed
    private val totalTimer: StopWatch = new StopWatch()
    private var compiler: Option[LogicCompiler] = None
    private var solverSession: Option[Solver] = None
    private var compilerResult: Option[CompilerResult] = None

    /** Create a compiler using the given integer semantics. */
    protected def createCompiler(): LogicCompiler
    
    override def checkSat(verbose: Boolean = false): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()

        compiler = Some(createCompiler())

        compiler.get.compile(theory, analysisScopes, timeoutMilliseconds, eventLoggers.toList, verbose) match {
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
        
        // Close solver session, if one exists
        solverSession.foreach(_.close())
        
        // Open new solver session
        val session = solverInterface.openSession()
        solverSession = Some(session)

        // Convert to solver format
        notifyLoggers(_.convertingToSolverFormat())
        val (_, elapsedConvertNano) = measureTime[Unit] {
            session.setTheory(finalTheory)
        }
        notifyLoggers(_.convertedToSolverFormat(elapsedConvertNano))

        // Solve
        val (finalResult, elapsedSolverNano) = measureTime {
            val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
            session.solve(remainingMillis)
        }
        notifyLoggers(_.solverFinished(elapsedSolverNano))

        notifyLoggers(_.finished(finalResult, totalTimer.elapsedNano()))

        finalResult
    }
    
    def viewModel: Interpretation = {
        val instance = solverSession.get.solution
        compilerResult.get.decompileInterpretation(instance)
    }

    def nextInterpretation(): ModelFinderResult = {
        // Negate the current interpretation, but leave out the skolem functions
        // Different witnesses are not useful for counting interpretations
        val instance = solverSession.get.solution
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

        solverSession.get.addAxiom(newAxiom)
        solverSession.get.solve(timeoutMilliseconds)
    }

    override def countValidModels(newTheory: Theory): Int = {
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
    
    override def close(): Unit = {
        solverSession.foreach(_.close())
    }
}
