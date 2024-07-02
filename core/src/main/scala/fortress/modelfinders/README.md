# `fortress.modelfinders` Package

The `fortress.modelfind` package contains the `ModelFinder` trait (interface).
A `ModelFinder` is an object that accepts an input theory and scopes, and determines whether the theory is satisfiable or not with respect to those scopes.
It is the main interface a user of Fortress makes use of.  The user can set the compiler, solver, timeout, etc.

**ModelFinderRegistry.scala must be kept up-to-date as a mapping from strings to class names for model finders that the user can choose**