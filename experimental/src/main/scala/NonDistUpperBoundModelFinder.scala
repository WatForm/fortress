package fortress.modelfind

import fortress.solverinterface.SolverInterface
import fortress.solverinterface.Z3IncCliInterface
import fortress.compiler._

class NonDistUpperBoundModelFinder(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new NonDistUpperBoundCompiler
}