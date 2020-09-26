# `fortress.solverinterface` Package

The `fortress.solverinterface` package is Fortress's way of connecting to external solvers.
The important trait (interface) is the `SolverStrategy`, which is the abstract representation of communicating between Fortress and an external solver.
The abstract `SolverTemplate` class, which implements `SolverStrategy`, provides more details of the communication protocol, but does not directly talk to any solvers.
Concrete implementations of `SolverTemplate` directly talk to external solvers.
