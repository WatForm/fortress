# Fortress

Fortress is a library for finite model finding in typed (or "many-sorted") first order logic (TFOL) with equality.
Fortress consists of two main parts:
* An internal Domain Specific Language (DSL) in Java for creating TFOL formulas and theories, and
* A tool for searching for finite models that satisfy such theories

It was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions", [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

## Setup
We currently have setup tested on `MacOS` and `Ubuntu`.

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
    * `libz3java.dylib` in `fortress-2.0/z3`, if running `MacOS`, and
    * `libz3java.so` in `fortress-2.0/z3`, if running `Ubuntu`.
3. Install the Microsoft Z3 command line tool, version 4.8.4 or higher. Binaries are available in the above zip file.
    * If using MacOS, I recommend using Homebrew instead: `brew install z3`.
    * If on `Ubuntu`, do not use `apt-get`. Its version of Z3 is out of date.

## Building Fortress
Fortress uses the Gradle build system.
If running Windows, substitute `./gradlew` for `gradle.bat` in all commands.
Any use of `./gradlew` will automatically download the appropriate version of the build system, as well any additional dependencies for fortress.

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
1. Follow the steps for building Fortress.
2. Copy `build/distributions/fortress-2.0.tar` or `build/distributions/fortress-2.0.jar` to an appropriate location, such as a `libs` folder for your project.
3. Unzip the archive.
4. When compiling and running, ensure that the files from this archive are in your Java `classpath`.
    * For example, if the files are in the `libs` directory of your project, you can add `-cp ".:libs/*"` to `javac`, which says to look for class files in current directory and also jars in the libs directory.
5. When running, ensure that the `libz3java.dylib` or `libz3java.so` file from this archive is in your `java.library.path`.
    * For example, if `libz3java.dylib` is in the `libs` directory, you can add `-Djava.library.path="libs/"` to your call to `java`.
    * If this is not done correctly, a `java.lang.UnsatisfiedLinkError` may be raised at runtime.
