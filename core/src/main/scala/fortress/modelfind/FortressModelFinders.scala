package fortress.modelfind

import fortress.solverinterface._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import fortress.symmetry._
import fortress.compiler._
import fortress.config.Manager

class FortressZERO(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new FortressZEROCompiler()
}

class FortressONE(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)
    
    override def createCompiler(): LogicCompiler = new FortressONECompiler()
}

class FortressTWO(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)
    
    override def createCompiler(): LogicCompiler = new FortressTWOCompiler()
}

class FortressTWO_SI(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)
    
    override def createCompiler(): LogicCompiler = new FortressTWOCompiler_SI()
}

class FortressTHREE(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)
    
    override def createCompiler(): LogicCompiler = new FortressTHREECompiler()
}

class FortressTHREE_SI(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)
    
    override def createCompiler(): LogicCompiler = new FortressTHREECompiler_SI()
}

class FortressFOUR(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new FortressFOURCompiler()
}

class FortressFOUR_SI(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new FortressFOURCompiler_SI()
}

class FortressUnbounded(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new FortressUnboundedCompiler()
}

class FortressLearnedLiterals(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new FortressLearnedLiteralsCompiler()
}

class NonDistUpperBoundModelFinder(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new NonDistUpperBoundCompiler
}

class PredUpperBoundModelFinder(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {
    def this() = this(Z3IncCliInterface)

    override def createCompiler(): LogicCompiler = new PredUpperBoundCompiler
}

class ConfigurableModelFinder(solverInterface: SolverInterface, configManager: Manager) extends CompilationModelFinder(solverInterface) {
    def this(configManager: Manager) = this(Z3IncCliInterface, configManager)

    override def createCompiler(): LogicCompiler = configManager.setupCompiler()
}


object FortressModelFinders {
    def fromString(str: String, solverInterface: SolverInterface = Z3CliInterface): Option[ModelFinder] = {
        str.toLowerCase() match {
            case "zero" | "fortresszero" => Some(new FortressZERO(solverInterface))
            case "one" | "fortressone" => Some(new FortressONE(solverInterface))
            case "two" | "fortresstwo" => Some(new FortressTWO(solverInterface))
            case "two_si" | "fortresstwo_si" => Some(new FortressTWO_SI(solverInterface))
            case "three" | "fortressthree" => Some(new FortressTHREE(solverInterface))
            case "three_si" | "fortressthree_si" => Some(new FortressTHREE_SI(solverInterface))
            case "four" | "fortressfour" => Some(new FortressFOUR(solverInterface))
            case "four_si" | "fortressfour_si" => Some(new FortressFOUR_SI(solverInterface))
            case "mixed_scope" =>Some( new PredUpperBoundModelFinder(solverInterface))
            case _ => None
        }
    }
}


/**
  * A Model finder that allows the user to directly specify the compiler to use
  *
  * @param solverInterface the solver interface to be used
  * @param compiler the compiler the problem will be passed through before being given to the solver
  */
class SimpleModelFinder(solverInterface: SolverInterface, compiler: LogicCompiler) extends CompilationModelFinder(solverInterface) {
    def this(compiler: LogicCompiler) = this(Z3IncCliInterface, compiler)

    def this(solverInterface: SolverInterface, transformers: Seq[ProblemStateTransformer]) = this(solverInterface, new ConfigurableCompiler(transformers))

    def this(transformers: Seq[ProblemStateTransformer]) = this(new ConfigurableCompiler(transformers))

    def this(solverInterface: SolverInterface, transformers: Array[ProblemStateTransformer]) = this(solverInterface, new ConfigurableCompiler(transformers))


    def this(transformers: Array[ProblemStateTransformer]) = this(new ConfigurableCompiler(transformers))

    override protected def createCompiler(): LogicCompiler = compiler
}