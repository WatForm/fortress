# Fortress

Fortress is a command-line tool and library for manipulating many-sorted first order logic (MSFOL) (plus transitive closure and hopefully soon, set cardinality) formulas with SMT solvers. In particular, given scopes for all the sorts of the problem, Fortress can transform problems into formulas within the equality with uninterpreted functions decidable subset of MSFOL.

Fortress takes as input:
* a first-order logic theory specified in SMT-LIB 2.6 format, and
* (usually) a domain size ("scope") for each sort.

It answers whether the theory has a satisfying interpretation (a "model" or "solution") with the given domain sizes.

Fortress was originally described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

Details on using Fortress as the command line are available [in this file](#using-the-fortress-cli). The fortress CLI take as input a file in an augmented SMT-LIB format.

Details on using Fortress as a library are available in UserGuide.md .

Details on the internal code organization and design decisions in Fortress can be found in DevelopersGuide.md .

## Building Fortress
The following are necessary to build Fortress:
* Java 10 or higher
* A command line installation of the `Z3` SMT solver, version 4.8.15 or higher.
    * Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`, since its version of Z3 is out of date.
    * We have not successfully built fortress on Windows yet, however, if built elsewhere the jars should work on Windows.
* If using CVC4, a command line installation of the `CVC4` SMT solver.
    * If using MacOS, we recommend using Homebrew: `brew tap cvc4/cvc4 && brew install cvc4`.
* The sbt build tool.

### Build System Overview
This repository contains a multi-project sbt build, with the following projects:
* `fortressCore`, the main functionality of Fortress
* `fortress`, the command line interface of Fortress (depends on `fortressCore`)
* `fortressDebug`, a command line interface for debugging Fortress (depends on `fortressCore`)
* `root`, the root project which aggregates `fortress` and `fortressDebug`

Building the `root` project (default) is the easiest way to build Fortress.
To use Fortress on the command line, you want the output from the `fortress` project.

You can read more about how to use multi-project builds in the [sbt reference manual](https://www.scala-sbt.org/1.x/docs/index.html).

### Complete Build
```
sbt stage
```
This will compile the code and produce executables:
* For the `fortress` project, the executable is `./cli/target/universal/stage/bin/fortress`
* For the `fortressCore` project, there are 4 jars in `./core/target/universal/stage/lib/`
* For the `fortressDebug` project, the executable is `./debug/target/universal/stage/bin/fortressdebug`

Alternatively,
```
sbt dist
```
will compile the code produce universal zip archives:
* For the `fortress` project, the output zip is in the `cli/target/universal/fortress-x.y.z.zip` directory.
* For the `fortressCore` project, the output zip is in the `core/target/universal/fortresscore-x.y.z.zip` directory.
* For the `fortressDebug` project, the output zip is in the `debug/target/universal/fortressdebug-x.y.z.zip` directory.


### Compile Only
```
sbt compile
```

### Running Unit Tests
```
sbt test
```


## Using Fortress as a Library

Most often Fortress is used as a library.  You can either:
* put `./core/target/universal/stage/lib` (built by sbt stage) in your class path
or
* copy `./core/target/universal/fortresscore-0.1.0.zip` (built by sbt dist) somewhere, uzip it, and put that location in your class path.

All 4 jars must be in the class path.

Instructions on using the Fortress API interface can be found in the [API guide](APIGuide.md).



## Using the Fortress CLI

You can run the Fortress CLI, by either:
* `./cli/target/universal/stage/bin/fortress` (built by sbt stage)
or
* Unzipping `cli/target/universal/fortresscore-x.y.z.zip` and running `./cli/target/universal/fortresscli-0.1.0/bin/fortress` (built by sbt dist)

### Options for the Fortress CLI

The options to the Fortress CLI, can be found by running `fortress --help`. In addition:

* A filename is required of a file in an augmented [smttc file format](#smttc-file-format).

* The lists of possible modelFinders, compilers, solvers, and transformers can be found in the Registry files within the code, e.g., ./core/src/main/scala/fortress/compilers/CompilersRegistry.scala contains the Compiler names. But good defaults are used if these options are not provided in the command-line.

* A scope can be set with default values (`--scope`), individually on a sort by sort basis (`-S`), and in the input file.
    * A scope is set for a sort using the default scope (`--scope {SCOPE}` if provided), which is overwritten by a scope for the sort provided in the file, which is overwritten by a scope provided in the command-line argument `-S {SORT}={SCOPE}`. `-S` can take a sequence of `{SORT}={SCOPE}`s or it can be used multiple times in the command line.

Example usage:
```
fortress --timeout 30 -S A=3 B=2 --generate function.smttc
```
This creates a theory using the `function.smttc` file, and determines whether there is a satisfying interpretation for this theory where the scope of sort `A` is 3 and the scope of sort `B` is 2.
If a model exists, fortress outputs `Sat` and writes out the model (because of the `--generate` option).


## smttc File Format

Fortress reads (at the CLI or API) files in the smttc format. `.smttc` is a minor extension to the `.smt2` file format that includes a few special Fortress features.  These features are described below.

### Transitive Closure

smttc has a built-in operator for transitive closure.  Transitive closure expressions are written as `(closure R x y [fixedargs...])` or `(reflexive-closure R x y [fixedargs...])` for reflexive closure.

The term `(closure R start end)` evaluates to true if there is an edge from `start` to `end` in the transitive closure of `R`.
`R` should be the identifier for the relation to be closed over. `start` and `end` are terms.

Fortress also supports transitive closure over relations of higher airity.
Consider `R: A x A x B x C`. One can write `(closure R start end fixB fixC)` where `fixB` is a term of sort `B` and `fixC` is a term of sort `C`.
The closure then works as above over the relation `R'` where `(start, end) \in R'` if and only if `(start, end, fixB, fixC) \in R`.

### Scope Information

smttc supports three `set-info` keywords for setting scope information in the file:
- `:exact-scope` is used to set exact scopes
- `:nonexact-scope` is used to set non-exact scopes
- `:unchanging-scope` is used to specify which sorts Fortress is not allowed to change

Each of these keywords expects a string value. The `exact` and `nonexact` scope methods expect a series of optionally whitespace separated `(sort scope)` specifiers. Sort must be an identifier and scope must be an integer. There must be at least some amount of whitespace separating the sort and scope.

The specifier for unchanging scopes expects a series of `(sort)`s optionally separated by whitespace.

For example:
```smt2
(set-info :exact-scope "(A 1) (|Complicated Name!!| 3)")
(set-info :nonexact-scope "(B 2)")
(set-info :unchanging-scope "(A)(|Complicated Name!!|)")
```


## Developer's Guide

Information on the architecture of Fortress is available in the [Developer's Guide](DevelopersGuide.md).


## Using the Fortress CLI Debug Tools (Developers)

You can run the FortressDebug CLI, by either:
* `./debug/target/universal/stage/bin/fortressDebug`
or
* Unzipping `debug/target/universal/fortressdebug-x.y.z.zip` and running `./debug/target/universal/fortressdebug-0.1.0/bin/fortressdebug`

The options to the FortressDebug, can be found by running `fortressDebug --help`. In particular:
* `-S {SORT}={SCOPE}` - Sets the scope of a sort. This option can be used multiple times (the `-S` can be omitted after the first use).
* `--scope {SCOPE}` - Sets the default scope to use when a sort has no specified scope. This is overriden by `-S` for a specific sort.
* `-T {transformer1} {transformer2} ...` - Specify exactly which transformers will be used, in order.
* `--version {VERSION}`- Sets the model finder and compiler version. The options for versions can be found in the ./core/src/main/scala/fortress/modelFinders/ModelFindersRegistry.scala


Example usage:
```
fortressdebug --timeout 60 --mode count -S A=3 B=2 --version JoeONE function.smt2
```

You can increase the JVM stack size by setting option "-J-Xss<size>", for example, "-J-Xss8m" sets the max stack size to 8 MB. You might want to increase stack size, because the antlr parser causes stack overflow errors when parsing large smt2 and tptp files.

## Troubleshooting

If the gradle build is not working properly ensure that your `JAVA_HOME` environment variable is correctly set (to the folder where the jdk that you are using is installed).

## Acknowledgements

The original version of Fortress was created by Amirhossein Vakili and Nancy Day.  Fortress was completely rewritten in Scala by Joseph Poremba.  Joe also greatly extended the symmetry breaking used in Fortress.  Additional contributors to Fortress include: Ruomei Yan, Orson Baines, Callum Moseley, Yie Jin (James) Long, Ryan Dancy, and Owen Zila.

Some TPTP files publicly available on the TPTP Problem Library(http://www.tptp.org/) are used for unit tests.
