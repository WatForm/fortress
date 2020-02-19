# Overview

This directory contains examples of main programs that use the fortress library.

## Included examples
1. Smtlibparsemain.java: Uses Fortress Smtlibparser to parse an 
SMT-lIB file passed as an argument. Sets default scopes for all 
scopes (uses ?? for built-in Ints), calls default model finder 
(eufsolver/Z3) and prints result.
2. alg212.java: Uses Fortress API to create TPTP problem ALG212+1.p 
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
```
# Compile
javac -cp ".:libs/*" Pigeonhole.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" Pigeonhole 7 6
```
This example answers the question "Can you stuff 7 pigeons into 6 holes so that no hole has more than one pigeon in it?".
The numbers provided can be changed to change the number of pigeons and holes.
It will be satisfiable if and only if the number of pigeons is less than or equal to the number of holes.

### Latin Square
Run the following code to compile and run the Latin Square example.
```
# Compile
javac -cp ".:libs/*" LatinSquare.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" LatinSquare 3
```
This example finds a Latin Square of size 3.
The number provided can be changed to change the grid size.

### Latin Square with Clues
Run the following code to compile and run the Latin Square with Clues example.
```
# Compile
javac -cp ".:libs/*" LatinSquareClue.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" LatinSquareClue
```
This example finds a Latin Square of size 4 with the following entries already filled in.

|    | C1 | C2 | C3 | C4 |
|----|----|----|----|----|
| R1 |    |    |    | 1  |
| R2 | 3  |    |    |    |
| R3 |    |    | 2  |    |
| R4 |    | 4  |    |    |

### N Rooks - Relational Encoding
Run the following code to compile and run the relational N Rooks example.
```
# Compile
javac -cp ".:libs/*" RooksRelational.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" RooksRelational 5
```
This example finds a way to place 5 rooks on a 5 x 5 chessboard so that none of
the rooks are attacking each other (i.e. they are in different columns and
different rows).
This problem essentially boils down to finding a bijection between rows and columns.
In this example, the problem is encoded using a binary relation that says which
(row, column) pairs have rooks in them.
The number provided can be changed to change the number of rooks and grid size.
