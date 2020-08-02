# Fortress

Fortress is a library for finite model finding in many-sorted first order logic (MSFOL) with equality.

Fortress consists of two main parts:
* An internal Domain Specific Language (DSL) in Java for creating MSFOL formulas/theories/problems
* A tool for searching for finite models that satisfy such theories

Fortress is written in Scala, but is intended to be used by Java users and *not* Scala users.

It was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

## System Requirements
Fortress requires Java 10 or higher to build and run.

## Overview

To use Fortress, there are three steps:
1. Install the command line versions of the `Z3` and `CVC4` SMT solvers.
2. Build the Fortress code.
3. Use the Fortress library in your own project.

## Setup

The developers primarily use `MacOS`, with additional testing done on `Ubuntu`.
We do not currently test on `Windows`, but building and running Fortress should still work correctly.

Perform the following steps.

1. Install the Z3 command line tool, version 4.8.4 or higher. Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`, since its version of Z3 is out of date.
2. Install the latest stable version of the CVC4 command line tool. Binaries are [available here](https://cvc4.github.io/downloads.html). Make sure that the executable is named `cvc4` and is on your PATH. To make sure that cvc4 is properly installed, open up terminal and type `cvc4`. CVC4 should open in interactive mode.
    * If using MacOS, we recommend using Homebrew: `brew install cvc4`.

## Building Fortress
Java 10 or higher is required to build Fortress.
Fortress uses the Gradle build system through calls to `./gradlew` as described below.
If running Windows, run `gradle.bat` instead of `./gradlew` in the steps below.
Any use of `./gradlew` will automatically download the appropriate version of the build system, as well any additional dependencies for Fortress.

### Complete Build
Run `./gradlew build`.
This will compile the code, run unit tests, and produce archive files in both zip and tar formats that contain a Fortress jar and all of its runtime dependencies.
The archives will be located in `build/distributions`.

### Compiling
Run `./gradlew compileScala`.

### Running Unit Tests
Run `./gradlew test`.
Note that you may need to run `./gradlew cleanTest test` to run all of the tests, since Gradle may not run tests that it believes are up to date.

## Using the Fortress library in your own project

Follow the below instructions.
Check out the `examples/` directory for some examples of how to use Fortress in your own project.

1. Follow the steps for setting up and building Fortress (above).
2. Copy `build/distributions/fortress-2.0.tar` or `build/distributions/fortress-2.0.zip` (both archives contain the same files) to an appropriate location, such as a `libs` folder for your project.
3. Unzip the archive.
4. When compiling and running, ensure that the files from this archive are in your Java `classpath`.
    * For example, if the files are in the `libs` directory of your project, you can add `-cp ".:libs/*"` to `javac`, which says to look for class files in current directory and also jars in the libs directory.
    
## Troubleshooting

### General
If the gradle build is not working properly ensure that your `JAVA_HOME` environment variable is correctly set (to the folder where the jdk that you are using is installed).
