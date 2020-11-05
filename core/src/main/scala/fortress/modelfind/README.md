# `fortress.modelfind` Package

The `fortress.modelfind` package contains the `ModelFinder` trait (interface).
A `ModelFinder` is an object that accepts an input theory and scopes, and determines whether the theory is satisfiable or not with respect to those scopes.
It is the main interface a user of Fortress makes use of.

## Internal Notes
A `ModelFinder` is the main conductor, combining together the other pieces of Fortress.
Given an input theory, it applies various `TheoryTransformer`s in sequence to transform the problem to an equisatisfiable problem in a simpler logic.
Then, it calls on a `SolverStrategy` object to take this transformed theory and invoke an external solver (e.g. Z3) to solve the problem.
