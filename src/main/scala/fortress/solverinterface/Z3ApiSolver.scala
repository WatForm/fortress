package fortress.solverinterface

import fortress.msfol._
import fortress.util._

import fortress.modelfind._
import fortress.solverinterface._
import fortress.interpretation._

import com.microsoft.z3.{
    Model => Z3Model,
    Context => Z3Context,
    Solver => Z3Solver,
    Status => Z3Status,
    Params => Z3Params
}

class Z3ApiSolver extends SolverTemplate {
    private var lastModel: Option[Z3Model] = None
    private var context: Option[Z3Context] = None
    private var solver: Option[Z3Solver] = None
    private var converter: Option[TheoryToZ3_StringParse] = None

    override protected def convertTheory(theory: Theory): Unit = {
        converter = Some(new TheoryToZ3_StringParse(theory))
        val pair: (Z3Context, Z3Solver) = converter.get.convert
        context = Some(pair._1)
        solver = Some(pair._2)
    }

    override def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult = {
        solver.get.push()
        solver.get.add(converter.get.convertAxiom(axiom))

        updateTimeout(timeoutMillis)
        runSolver()
    }

    override protected def updateTimeout(remainingMillis: Milliseconds): Unit = {
        Errors.assertion(context.nonEmpty)
        Errors.assertion(solver.nonEmpty)

        val params: Z3Params = context.get.mkParams()
        params.add("timeout", remainingMillis.value)
        solver.get.setParameters(params)
    }

    @throws(classOf[java.io.IOException])
    override protected def runSolver(): ModelFinderResult = {
        Errors.assertion(context.nonEmpty)
        Errors.assertion(solver.nonEmpty)

        val status: Z3Status = solver.get.check()
        lastModel = None
        status match {
            case Z3Status.UNKNOWN => {
                // TODO timeout errors
                // log.write("UNKNOWN (" + solver.get.getReasonUnknown() + ").\n")
                if(solver.get.getReasonUnknown() == "timeout"
                        || solver.get.getReasonUnknown == "canceled") {
                    return ModelFinderResult.Timeout
                }
                return ModelFinderResult.Unknown
            }
            case Z3Status.SATISFIABLE => {
                lastModel = Some(solver.get.getModel())
                // log.write("SAT.\n")
                return ModelFinderResult.Sat
            }
            case Z3Status.UNSATISFIABLE => {
                // log.write("UNSAT.\n")
                return ModelFinderResult.Unsat
            }
            case _ => throw new java.lang.RuntimeException("Unexpected solver result " + status.toString)
        }
    }

    def getInstance(theory: Theory): Interpretation = {
        Errors.assertion(lastModel.nonEmpty, "There is no current instance")
        return new Z3ApiInterpretation(lastModel.get, theory.signature, converter.get, context.get)
    }
}
