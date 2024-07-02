# `fortress.compilers` Package

The `fortress.compilers` package is the way Fortress packages the logical transformations on
a theory before it is given to a solver.

A compiler is a sequence of transformers.  There are some flags used in the transformers that
ensure certain transformers are done before others. These flags are contained in the ProblemState.

One file contains compilers tried in one project.

The compilers classes are arranged hierarchically:
trait Compiler
	- StandardCompiler - default is constants method but with common variation points
		+ ClaessenCompiler
		+ DatatypeNoRangeEUFCompiler
		+ DatatypeWithRangeCompiler
			* DatatypeNoRangeCompiler
	- JoeSymmetryCompilers - compilers testing symmetry breaking and sort inference (IEEE TSE 2023)
	- ConfigurableCompiler - ???
	- trait PervasiveTypeChecking - adds typechecking between all transformers as a check

CompilerResult/CompilerError - return values from the compile phase.

**CompilerRegistry.scala must be kept up-to-date as a mapping from strings to class names for compilerss that the user can choose.**