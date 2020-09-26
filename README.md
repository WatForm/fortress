# Fortress

Fortress is a command-line tool for finite model finding in many-sorted first order logic (MSFOL) with equality.

Fortress takes as input:
* a first-order logic theory specified in SMT-LIB 2.6 format (the UF fragment), and
* a domain size ("scope") for each sort.

It answers whether the theory has a satisfying interpretation with respect to those domain sizes.

Fortress was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

## Using Fortress

### System Requirements
The following are necessary to run Fortress:
* Java 10 or higher. 
* A command-line installation of the `Z3` SMT solver, version 4.8.4 or higher.
    * Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`, since its version of Z3 is out of date.

### Running Fortress
After unzipping `fortress-x.y.z.jar`, and adding its `bin` directory to your PATH, run Fortress using the `fortress` command.

Options:
* `--mode {MODE}` - Sets the mode. The options are `decision`, `count`, and `compile`.
* `--version {VERSION}`- Sets the version. The options are `v0`, `v1`, `v2`, `v2si`, `v3`, and `v3si`.
* `-S {SORT}={SCOPE}` - Sets the scope of a sort.
* `--scope {SCOPE}` - Sets the default scope to use when a sort has no specified scope. This is overriden by `-S` for a specific sort.

Example usage:
```
fortress --mode decision -S A=3 B=2 --version v0 function.smt2
```
This generates a theory using the `function.smt2` file, and determines whether there is a satisfying interpretation for this theory where the scope of sort `A` is 3 and the scope of sort `B` is 2.

## Building Fortress
The following are necessary to build Fortress:
* Java 10 or higher
* A command line installation of the `Z3` SMT solver, version 4.8.4 or higher.
    * Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`, since its version of Z3 is out of date.
* A command line installation of the `CVC4` SMT solver.
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

### Complete Build
Run `sbt dist`.
This will compile the code produce universal zip archives:
* For the `fortress` project, the output zip is in the `cli/target/universal/` directory.
* For the `fortressCore` project, the output zip is in the `core/target/universal/` directory.
* For the `fortressDebug` project, the output zip is in the `debug/target/universal/` directory.

### Compile Only
Run `sbt compile`.

### Running Unit Tests
Run `sbt test`.
    
## Troubleshooting

### General
If the gradle build is not working properly ensure that your `JAVA_HOME` environment variable is correctly set (to the folder where the jdk that you are using is installed).
