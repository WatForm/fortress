# `fortress.compilers` Package

The `fortress.compilers` package contains the `Compiler` class.  

A `Compiler` is a sequence of transformers.  This is the way Fortress packages the logical transformations on a theory before it is given to a solver.

See the file Compiler.scala for the interface functions.

There are some flags used in the transformers that
ensure certain transformers are done before others. These flags are contained in the ProblemState.

The Compilers used in one project are usually packaged together in one file.

The Compiler's subclasses are arranged hierarchically:
trait Compiler
    - BaseCompiler - defns used in all compilers
		+ StandardCompiler - default is constants method but with common variation points
			* ClaessenCompiler
			* DatatypeWithRangeEUFCompiler
				- DatatypeNoRangeEUFCompiler
			* DatatypeWithRangeNoEUFCompiler
				- DatatypeNoRangeNoEUFCompiler
		+ JoeSymmetryCompilers - compilers testing symmetry breaking and sort inference (IEEE TSE 2023)
	- ConfigurableCompiler - provides more flexibility in setting the set of transformers for the compiler
	- trait PervasiveTypeChecking - adds typechecking between all transformers as a check

CompilerResult/CompilerError - return values from the compile phase.

**CompilerRegistry.scala must be kept up-to-date as a mapping from strings to class names for compilers that the user can choose.**