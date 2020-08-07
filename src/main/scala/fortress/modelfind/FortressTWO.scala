package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import fortress.compiler._

class FortressTWO(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new FortressTWOCompiler(integerSemantics)
}

class FortressTWO_G(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new FortressTWOCompiler_G(integerSemantics)
}

class FortressTWO_R(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3CliInterface)
    
    override def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler = new FortressTWOCompiler_R(integerSemantics)
}
