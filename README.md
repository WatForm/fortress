# Fortress

Fortress is a library for finite model finding in typed (or "many-sorted") first order logic (TFOL) with equality.
Fortress consists of two main parts:
* An internal Domain Specific Language (DSL) in Java for creating TFOL formulas and theories, and
* A tool for searching for finite models that satisfy such theories

It was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

To use fortress, there are three steps: 1) setup (install supporting libraries); 2) build the fortress code; 3) use the fortress library in your own project.  Each of these steps are described below.

## Setup
We currently have setup scripts tested on `MacOS` and `Ubuntu`.  Otherwise, follow the manual setup sets described below.

### Setup Scripts
Scripts are available to automate some of the setup for the following platforms:
* MacOS (`setup_macos.sh`)
* Ubuntu 16.04 (`setup_ubuntu_16.04.sh`)
* Ubuntu 14.04 (`setup_ubuntu_14.04.sh`)

1. Run the appropriate setup script for your platform.
2. Install the Z3 command line tool, version 4.8.4 or higher. Binaries are [available here](https://github.com/Z3Prover/z3/releases).
    * If using MacOS, I recommend using Homebrew instead: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`. Its version of Z3 is out of date.

### Manual Setup
1. Clone the `fortress-2.0` repository.
2. Download all required files for the Microsoft Z3 SMT solver. These can be found in a zip file, [available here](https://github.com/Z3Prover/z3/releases).
    We have used Z3 4.8.4.
    Specifically you will need to place the following files in the corresponding locations:
    * `com.microsoft.z3.jar` in `fortress-2.0/z3/`,
    * `libz3java.dylib` in `fortress-2.0/z3`, if running `MacOS`,
    * `libz3java.so` in `fortress-2.0/z3`, if running `Ubuntu`, and
    * `libz3java.dll` in `fortress-2.0/z3`, if running `Windows`.
3. Install the Microsoft Z3 command line tool, version 4.8.4 or higher. Binaries are available in the above zip file.
    * If using MacOS, I recommend using Homebrew instead: `brew install z3`.
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
Run `./gradlew compileJava`.

### Running Unit Tests
Run `./gradlew test`.
Note that you may need to run `./gradlew cleanTest test` to run all of the tests, since Gradle may not run tests that are up to date.

### Building Documentation
Run `./gradlew javadoc`.

## Running Fortress in Your Project
Follow the steps in examples/README.md

