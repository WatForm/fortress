# Fortress

Fortress is a command-line tool and library for finite model finding in many-sorted first order logic (MSFOL) with equality.

Fortress takes as input:
* a first-order logic theory specified in SMT-LIB 2.6 format (the UF fragment), and
* a domain size ("scope") for each sort.

It answers whether the theory has a satisfying interpretation (a "model" or "solution") with the given domain sizes.

Fortress was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.  

Details on using Fortress as the command line are available in this file.

Details on using  Fortress as a library are available in UserGuide.md .  

Details on the internal code organization and design decisions in Fortress can be found in DevelopersGuide.md .

## Building Fortress
The following are necessary to build Fortress:
* Java 10 or higher
* A command line installation of the `Z3` SMT solver, version 4.8.4 or higher.
    * Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`, since its version of Z3 is out of date.
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
sbt dist
```
This will compile the code produce universal zip archives:
* For the `fortress` project, the output zip is in the `cli/target/universal/` directory.
* For the `fortressCore` project, the output zip is in the `core/target/universal/` directory.
* For the `fortressDebug` project, the output zip is in the `debug/target/universal/` directory.

### Compile Only
```
sbt compile
```

### Running Unit Tests
```
sbt test
```

## Using Fortress


### Running Fortress
After unzipping `fortress-x.y.z.jar`, and adding its `bin` directory to your PATH, run Fortress using the `fortress` command.

Options:
* `--timeout {SECONDS}`- Sets the timeout in seconds.
* `-S {SORT}={SCOPE}` - Sets the scope of a sort. This option can be used multiple times (the `-S` can be omitted after the first use).
* `--scope {SCOPE}` - Sets the default scope to use when a sort has no specified scope. This is overriden by `-S` for a specific sort.
* `--generate` - Generate a model if one exists.

Example usage:
```
fortress --timeout 30 -S A=3 B=2 --generate function.smt2
```
This creates a theory using the `function.smt2` file, and determines whether there is a satisfying interpretation for this theory where the scope of sort `A` is 3 and the scope of sort `B` is 2.
Such a model exists, so the program outputs `Sat` and writes out the model.

### Running Fortress Debug Tools (Developers)
After unzipping `fortressdebug-x.y.z.jar`, run the debug tools using the `./fortressdebug-x.y.z/bin/fortressdebug` command.

Options:
* `--timeout {SECONDS}`- Sets the timeout in seconds.
* `-S {SORT}={SCOPE}` - Sets the scope of a sort. This option can be used multiple times (the `-S` can be omitted after the first use).
* `--scope {SCOPE}` - Sets the default scope to use when a sort has no specified scope. This is overriden by `-S` for a specific sort.
* `--mode {MODE}` - Sets the mode. The options are `decision` (sat/unsat), `count` (count sat instances), `compile` (convert to smt2), `checkfornewsorts` (determines if any new sorts appear in type inference).
* `--version {VERSION}`- Sets the model finder and compiler version. The options are `v0`, `v1`, `v2`, `v2si`, `v3`, and `v3si` (more are being added).
* `--debug`- Sets this flag to get more information about execution time.
* `--rawdata`- Sets this flag to get log information in machine-friendly format, so that data can be easily collected for data analysis purpose
* `--validate`- Sets this flag to verify the instance returned by solver satisfies the original theory before applying transformation for SAT models.
* `--view-model`- Sets this flag to display an interpretation that satisfies the model.

Example usage:
```
./fortressdebug-x.y.z/bin/fortressdebug --timeout 60 --mode count -S A=3 B=2 --version v0 function.smt2
```

You can increase the JVM stack size by setting option "-J-Xss<size>", for example, "-J-Xss8m" sets the max stack size to 8 MB. You might want to increase stack size, because the antlr parser causes stack overflow errors when parsing large smt2 and tptp files.
    
## Troubleshooting

If the gradle build is not working properly ensure that your `JAVA_HOME` environment variable is correctly set (to the folder where the jdk that you are using is installed).

## Acknowledgements

The original version of Fortress was created by Amirhossein Vakili and Nancy Day.  Fortress was completely rewritten in Scala by Joseph Poremba.  Joe also greatly extended the symmetry breaking used in Fortress.  Additional contributors to Fortress include: Ruomei Yan, Orson Baines, Callum Moseley, Yie Jin (James) Long, and Owen Zila.
   
Some TPTP files publicly available on the TPTP Problem Library(http://www.tptp.org/) are used for unit tests.
