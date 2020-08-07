package fortress.modelfind

import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.solverinterface._
import fortress.interpretation._
import fortress.operations._
import fortress.symmetry._
import fortress.compiler._

class FortressTWO_SI(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new FortressTWOCompiler_SI(integerSemantics)
}
