# `fortress.solverinterface` Package

The `fortress.solverinterface` package is Fortress's way of connecting to external solvers.

Trait SolverInterface provides an interface to all solvers  .openSession() creates a particular solver.

Solver is a trait that solvers are instances of.

The solvers are arranged hierarchically:
Solver
	- SMTLIBCliSolver - common function for interfacing with SMTLIB solvers are the cmd-line
		+ CVC4CliSolver
		+ Z3NonIncCliSolver

ProcessSession is an extra class used by SMTLIBCLiSolver to use Java's ProcessBuilder interface.

TODO:
- remove SolverInterface after a solver is set directly in the ModelFinder
