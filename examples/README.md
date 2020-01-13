# Overview

This directory contains examples of main programs that use the fortress library.

## Included examples
1. Sudoko.java: Uses Fortress API to create a 4x4 Suduko puzzle using a 
set of four enumerated values (so no scope has to be set), calls 
default model finder (eufsolver/Z3) and prints result.
2. Smtlibparsemain.java: Uses Fortress Smtlibparser to parse an 
SMT-lIB file passed as an argument. Sets default scopes for all 
scopes (uses ?? for built-in Ints), calls default model finder 
(eufsolver/Z3) and prints result.
3. alg212.java: Uses Fortress API to create TPTP problem ALG212+1.p 
(TPTP version 7.2.0).  The scope for the universal sort is passed as an 
argument, calls default model finder (eufsolver/Z3) and prints result.

## Automatic Compilation of Examples
1. ./gradlew <name-of-example> (or gradle.bat if on windows)

## Running Fortress in Your Project (or to compile the above examples)
1. Follow the steps for building Fortress.
2. Copy `build/distributions/fortress-2.0.tar` or `build/distributions/fortress-2.0.zip` (both archives contain the same files) to an appropriate location, such as a `libs` folder for your project. 
3. Unzip the archive.
4. When compiling and running, ensure that the files from this archive are in your Java `classpath`.
    * For example, if the files are in the `libs` directory of your project, you can add `-cp ".:libs/fortress-2.0/*"` to `javac`, which says to look for class files in current directory and also jars in the libs directory. 
5. When running, ensure that the `libz3java.dylib` or `libz3java.so` file from this archive (usually in the z3 directory) is in your `java.library.path`.
    * For example, if `libz3java.dylib` is in the `libs` directory, you can add `-Djava.library.path="libs/fortress-2.0"` to your call to `java`.
    * If this is not done correctly, a `java.lang.UnsatisfiedLinkError` may be raised at runtime.


