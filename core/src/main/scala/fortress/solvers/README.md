# `fortress.solvers` Package

The `fortress.solvers` package is Fortress's way of connecting to external solvers.

Solver is a trait that solvers are instances of.

The solver classes are arranged hierarchically:
Solver
	- SMTLIBCliSolver - common function for interfacing with SMTLIB solvers are the cmd-line
		+ CVC4CliSolver
		+ Z3NonIncCliSolver

ProcessSession is an extra class used by SMTLIBCLiSolver to use Java's ProcessBuilder interface.

**SolverRegistry.scala must be kept up-to-date as a mapping from strings to class names for solvers that the user can choose**