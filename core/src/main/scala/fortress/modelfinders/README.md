# `fortress.modelfinders` Package

The `fortress.modelfinders` package contains the `ModelFinder` class.

A `ModelFinder` is an object that accepts an input theory and scopes, and determines whether the theory is satisfiable or not with respect to those scopes for fortress.  

See the file ModelFinder.scala for the interface functions.

Class Hierarchy:
ModelFinder (just the interface)
	- StandardModelFinder (default definitions for interface functions using StandardCompiler, Z3NonIncCliSolver)
		+ JoeModelFinders (and more below used in Joe's Symmetry Breaking IEEE TSE) 
		+ ConfigurableModelFinder (allows compiler, solver to be parameters to the class and allows sequences of transformers as parameters)

The ModelFinders used in one project are usually packaged together in one file.

**ModelFinderRegistry.scala must be kept up-to-date as a mapping from strings to class names for model finders that the user can choose**