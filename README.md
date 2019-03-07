# Fortress

Fortress is a library for finite model finding in typed (or "many-sorted") first order logic with equality.
Fortress consists of two main parts:
* An internal Domain Specific Language (DSL) in Java for creating formulas and theories in typed first order logic, and
* A tool for searching for finite models that satisfy such theories

It was original described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions" by Amirhossein Vakili and Nancy Day, [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf), and has been re-implemented to create a powerful and general tool.

## Building Fortress
1. Clone the `fortress-2.0` repository.
2. Download all required files for the Microsoft Z3 SMT solver. These can be found in a zip file, [available here](https://github.com/Z3Prover/z3/releases).
    We have used Z3 4.8.4.
    Specifically you will need to place the following files in the corresponding locations:
    * `com.microsoft.z3.jar` in `fortress-2.0/z3/`, and
    * `libz3java.dylib` in `fortress-2.0/z3`.
3. Run `./gradlew build`.
    This will automatically download the appropriate version of the build system, as well as any additional dependencies for Fortress.
    It will also produce archive files in both zip and tar formats that contain a Fortress jar and all of its runtime dependencies.

## Running Unit Tests
1. Run `./gradlew cleanTest`.
2. Run `./gradlew test`.

## Running Fortress in Your Project
