# Fortress

Fortress is a library for finite model finding in many-sorted first order logic (MSFOL) with equality.

Fortress consists of two main parts:
* An internal Domain Specific Language (DSL) in Java for creating MSFOL formulas/theories/problems
* A tool for searching for finite models that satisfy such theories

Fortress is written in Scala, but is intended to be used by Java users and *not* Scala users.

It was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

## System Requirements
Fortress requires Java 10 or higher to compile and run.

## Overview

To use Fortress, there are three steps:
1. Setup  (install supporting libraries) - either by our scripts or manually
2. Build the Fortress code
3. Use the Fortress library in your own project

## Setup

We currently have setup scripts tested on `MacOS` and `Ubuntu`.  Otherwise, follow the manual setup sets described below.

### Setup Scripts
Scripts are available to automate some of the setup for the following platforms:
* MacOS (`setup_macos.sh`)
* Ubuntu 16.04 (`setup_ubuntu_16.04.sh`)
* Ubuntu 14.04 (`setup_ubuntu_14.04.sh`)

1. Run the appropriate setup script for your platform.
2. Install the Z3 command line tool, version 4.8.4 or higher. Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, we recommend using Homebrew instead: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`. Its version of Z3 is out of date.

### Manual Setup
1. Download all required files for the Microsoft Z3 SMT solver. These can be found in a zip file, [available here](https://github.com/Z3Prover/z3/releases).
    We have used Z3 4.8.4.
    Specifically you will need to place the following files in the corresponding locations:
    * `com.microsoft.z3.jar` in `fortress-2.0/z3/`,
    * `libz3java.dylib` in `fortress-2.0/z3`, if running `MacOS`,
    * `libz3java.so` in `fortress-2.0/z3`, if running `Ubuntu`, and
    * `libz3java.dll` in `fortress-2.0/z3`, if running `Windows`.
2. Install the Microsoft Z3 command line tool, version 4.8.4 or higher. Binaries are available in the above zip file.
    * If using MacOS, we recommend using Homebrew instead: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`. Its version of Z3 is out of date.
    * If on `Windows`, make sure you add the directory with `libz3java.dll` to your PATH.

## Building Fortress

Java 10 or higher is required to build Fortress.
Fortress uses the Gradle build system through calls to gradlew as described below. If running Windows, run gradle.bat instead of `./gradlew` in the steps below.  Any use of `./gradlew` will automatically download the appropriate version of the build system, as well any additional dependencies for fortress.

### Complete Build
Run `./gradlew build`.
This will compile the code, run unit tests, and produce archive files in both zip and tar formats that contain a Fortress jar and all of its runtime dependencies.
The archives will be located in `build/distributions`.

### Compiling
Run `./gradlew compileScala`.

### Running Unit Tests
Run `./gradlew test`.
Note that you may need to run `./gradlew cleanTest test` to run all of the tests, since Gradle may not run tests that are up to date.

### Building Documentation
Run `./gradlew javadoc`.

## Use the Fortress library in your own project

Follow the below instructions.
Check out the `examples/` directory for some examples of how to use Fortress in your own project.

1. Follow the steps for building Fortress (above).
2. Copy `build/distributions/fortress-2.0.tar` or `build/distributions/fortress-2.0.zip` (both archives contain the same files) to an appropriate location, such as a `libs` folder for your project. 
3. Unzip the archive.
4. When compiling and running, ensure that the files from this archive are in your Java `classpath`.
    * For example, if the files are in the `libs` directory of your project, you can add `-cp ".:libs/*"` to `javac`, which says to look for class files in current directory and also jars in the libs directory. 
5. When running, ensure that the `libz3java.dylib` or `libz3java.so` file from this archive (usually in the z3 directory) is in your `java.library.path`.
    * For example, if `libz3java.dylib` is in the `libs` directory, you can add `-Djava.library.path="libs/"` to your call to `java`.
    * If this is not done correctly, a `java.lang.UnsatisfiedLinkError` may be raised at runtime.
    
## Troubleshooting

### General
If the gradle build is not working properly ensure that your `JAVA_HOME` environment variable is correctly set (to the folder where the jdk that you are using is installed).

### Linux 
If you have double checked that you have correctly set the `-Djava.library.path` flag and a `java.lang.UnsatisfiedLinkError` is still being thrown, you can try copying the libz3java.so and libz3.so files to the /usr/lib directory and omitting the `-Djava.library.path` flag. It may also be useful to build Z3 from source following the instructions on the [Z3 Repository](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang) using the `--java` command line flag with `mk_make.py`.
