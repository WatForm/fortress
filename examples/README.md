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

## Setup
1. Follow the steps for building Fortress.
2. Copy and unzip the contents of `build/distributions/fortress-2.0.zip` into the `examples/libs` directory.
For example, the following shell code can be run from the `examples/` directory.
```
# Copy and unzip Fortress files into libs/ directory
rm -rf libs/fortress-2.0.zip libs/fortress-2.0.zip
cp ../build/distributions/fortress-2.0.zip libs/
unzip -oj libs/fortress-2.0.zip -d libs/
```

## Compiling and Running Examples
Change to the `examples/` directory before running the following code.
Make sure the `libs/` directory has been setup correctly.

### Pigeonhole
Run the following code to compile and run the Pigeonhole example.
The numbers can be changed to change the number of pigeons and holes.
```
# Compile
javac -cp ".:libs/*" Pigeonhole.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" Pigeonhole 10 10
```
