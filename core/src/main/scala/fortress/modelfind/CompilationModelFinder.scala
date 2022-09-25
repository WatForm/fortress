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
    private var solverSession: Option[solver] = None
    private var compilerResult: Option[CompilerResult] = None

    /** Create a compiler using the given integer semantics. */
    protected def createCompiler(): LogicCompiler
    
    override def checkSat(): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()

        compiler = Some(createCompiler())

        compiler.get.compile(theory, analysisScopes, timeoutMilliseconds, eventLoggers.toList) match {
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

        def forceValueToBool(term: Value): Boolean = term match{
            case Top => true
            case Bottom => false
            case _ => Errors.Internal.impossibleState("Tried to cast non-Top/Bottom Term to Boolean")
        }
        def boolToValue(b: Boolean): Value = if(b) Top else Bottom


        def getFunctionValue(fnName: String, evaluatedArgs: Seq[Value]): Value = {
            val funcDef = instance.functionDefinitions.filter(fd => fd.name == fnName).head
            val formalArgs: Seq[Term] = for( item <- funcDef.argSortedVar ) yield item.variable
            // transfer constants to domain elements, ex: p1 -> _@1P
            val realArgs: Seq[Value] = for( item <- evaluatedArgs ) yield {
                var temp: Value = item
                // TODO: look here! @zxt
//                for( a <- instance.constantInterpretations ) {
//                    if(a._1.variable.name == temp.toString ) temp = a._2
//                }
                temp
            }
            val body = funcDef.body
            Errors.Internal.precondition(evaluatedArgs.size == formalArgs.size, "Invalid input params.")
            val argMap: Map[Term, Value] = formalArgs.zip(realArgs).toMap
            val ret: Value = visitFunctionBody( body, argMap )
            ret
        }

        def visitFunctionBody(term: Term, argMap: Map[Term, Value]): Value = term match {
            case Top | Bottom | EnumValue(_) | DomainElement(_, _) |
                 IntegerLiteral(_) | BitVectorLiteral(_, _) => term.asInstanceOf[Value]
            case v @ Var(_) => argMap(v)
            case Not(p) => boolToValue(!forceValueToBool(visitFunctionBody(p, argMap)))
            case AndList(args) => boolToValue(args.forall(a => forceValueToBool(visitFunctionBody(a, argMap))))
            case OrList(args) => boolToValue(args.exists(a => forceValueToBool(visitFunctionBody(a, argMap))))
            case Distinct(args) => boolToValue(
                args.size == args.map(a => visitFunctionBody(a, argMap)).distinct.size
            )
            case Implication(p, q) => boolToValue(
                !forceValueToBool(visitFunctionBody(p, argMap)) || forceValueToBool(visitFunctionBody(q, argMap))
            )
            case Iff(p, q) => boolToValue(
                forceValueToBool(visitFunctionBody(p, argMap)) == forceValueToBool(visitFunctionBody(q, argMap))
            )
            case Eq(l, r) => boolToValue(visitFunctionBody(l, argMap) == visitFunctionBody(r, argMap))
            case IfThenElse(condition, ifTrue, ifFalse) => {
                if(forceValueToBool(visitFunctionBody(condition, argMap))) {
                    visitFunctionBody(ifTrue, argMap)
                }
                else {
                    visitFunctionBody(ifFalse, argMap)
                }
            }
            case App(fname, args) => getFunctionValue(fname, args.map(arg => visitFunctionBody(arg, argMap)))
            case BuiltinApp(fn, args) => evaluateBuiltIn(fn, args.map(arg => visitFunctionBody(arg, argMap)))
            case _ => {
                println("Error: get function value failed.")
                null
            }
        }

        // Given a builtin function and its arguments, run it through a throwaway Z3 solver for the result
        // (to avoid having to implement every function manually on our end)
        def evaluateBuiltIn(fn: BuiltinFunction, evalArgs: Seq[Value]): Value = {
            val evalResult: Var = Var("!VERIFY_INTERPRETATION_RES")
            val evalResultAnnotated: AnnotatedVar = fn match {
                case IntPlus | IntNeg | IntSub | IntMult | IntDiv | IntMod => evalResult of Sort.Int
                case BvPlus | BvNeg | BvSub | BvMult | BvSignedDiv | BvSignedRem | BvSignedMod =>
                    evalResult of Sort.BitVector(evalArgs.head.asInstanceOf[BitVectorLiteral].bitwidth);
                case IntLE | IntLT | IntGE | IntGT |
                     BvSignedLE | BvSignedLT | BvSignedGE | BvSignedGT => evalResult of Sort.Bool
                case _ => throw new scala.NotImplementedError("Builtin function not accounted for")
            }
            val theory: Theory = Theory.empty
                    .withConstant(evalResultAnnotated)
                    .withAxiom(evalResult === BuiltinApp(fn, evalArgs))

            val solver = new Z3IncSolver
            solver.setTheory(theory)
            solver.solve(Milliseconds(1000))
            val solvedInstance = solver.solution
            solver.close()
            solvedInstance.constantInterpretations(evalResultAnnotated)
        }

        val newInstance: Interpretation = {

            def scopes: Map[Sort, Int] = for((sort, seq) <- instance.sortInterpretations) yield (sort -> seq.size)

            val newFunctionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = {
                for(f <- theory.signature.functionDeclarations)
                    yield f -> {
                        for (argList <- ArgumentListGenerator.generate(f, scopes, Some(instance.sortInterpretations)))
                            yield argList -> getFunctionValue(f.name, argList)
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
