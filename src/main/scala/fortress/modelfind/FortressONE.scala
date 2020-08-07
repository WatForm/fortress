package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import fortress.compiler._

class FortressONE(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new FortressONECompiler(integerSemantics)
}