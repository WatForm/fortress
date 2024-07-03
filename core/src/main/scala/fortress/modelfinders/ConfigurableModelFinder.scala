package fortress.modelfinders

import fortress.problemstate._
import fortress.transformers._
import fortress.compilers._
import fortress.solvers._


/**
  * A Model finder that allows the user to directly specify the solver/compiler to use as parameters
  *
  * @param solver the solver interface to be used
  * @param compiler the compiler the problem will be passed through before being given to the solver
  *
  * there are a variety of constructors including Seq's of transformers
  * only used at API not CLI
  */
class ConfigurableModelFinder(solver: Solver, compiler: Compiler) extends StandardModelFinder() {

    this.setSolver(solver)
    this.setCompiler(compiler)

    def this(compiler: Compiler) = 
      this(new Z3NonIncCliSolver(), compiler)

    def this(solver: Solver, transformers: Seq[ProblemStateTransformer]) = 
      this(solver, new ConfigurableCompiler(transformers))

    def this(transformers: Seq[ProblemStateTransformer]) = 
      this(new ConfigurableCompiler(transformers))

    def this(solver: Solver, transformers: Array[ProblemStateTransformer]) = 
      this(solver, new ConfigurableCompiler(transformers))

    def this(transformers: Array[ProblemStateTransformer]) = 
      this(new ConfigurableCompiler(transformers))


}