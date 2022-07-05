# Overview

This directory contains examples of main programs that use the Fortress library.

<!-- ## Included examples
1. Smtlibparsemain.java: Uses Fortress Smtlibparser to parse an 
SMT-lIB file passed as an argument. Sets default scopes for all 
scopes (uses ?? for built-in Ints), calls default model finder 
(eufsolver/Z3) and prints result.
2. alg212.java: Uses Fortress API to create TPTP problem ALG212+1.p 
(TPTP version 7.2.0).  The scope for the universal sort is passed as an 
argument, calls default model finder (eufsolver/Z3) and prints result. -->

## Setup
1. Follow the steps for building Fortress.
2. Copy and unzip the contents of `build/distributions/fortress.zip` into the `examples/libs` directory.
For example, the following shell code can be run from the `examples/` directory.
```
# Copy and unzip Fortress files into libs/ directory
rm -rf libs/fortress.zip libs/fortress.zip
cp ../build/distributions/fortress.zip libs/
unzip -oj libs/fortress.zip -d libs/
```

## Compiling and Running Examples
Change to the `examples/` directory before running the following code.
Make sure the `libs/` directory has been setup correctly.
If you are on Windows use a semicolon to seperate paths in the -cp flag instead of a colon ie. `java -cp ".;libs/*" ...`

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

### Pigeonhole2
A copy of the Pigeonhole example utilizing the SimpleModelFinder.
```
# Compile
javac -cp ".:libs/*" Pigeonhole2.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" Pigeonhole2 7 6
```

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

### N Rooks - Functional Encoding
Run the following code to compile and run the functional N Rooks example.
```
# Compile
javac -cp ".:libs/*" RooksFunctional.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" RooksFunctional 5
```
This example finds a way to place 5 rooks on a 5 x 5 chessboard so that none of
the rooks are attacking each other (i.e. they are in different columns and
different rows).
This problem essentially boils down to finding a bijection between rows and columns.
In this example, the problem is encoded using a function from rows to columns.
If `rook(i) = j` then there is a rook in row i, column j.
The number provided can be changed to change the number of rooks and grid size.

### Non-Abelian Groups
Run the following code to compile and run the relational N Rooks example.
```
# Compile
javac -cp ".:libs/*" NonAbelianGroup.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" NonAbelianGroup 5
```
This example determines if there exists a non-abelian group of size 5.
The number provided can be changed to change the group size.
The problem is satisfiable if and only if there exists a non-abelian group of the given size.
Note that any prime sized group will yield UNSAT, since such groups are cyclic and cyclic groups are abelian.
[This link](https://en.wikipedia.org/wiki/List_of_small_groups#List_of_small_non-abelian_groups) describes for which sizes non-abelian groups exist.

### Infinite Ray
Run the following code to compile and run the Infinite Ray example.
```
# Compile
javac -cp ".:libs/*" InfiniteRay.java

# Run
# Note that -ea turns on assertions
java -ea -cp ".:libs/*" -Djava.library.path="libs" InfiniteRay 5
```
This example asks if there exists a graph on 5 vertices so that:
* there is exactly one vertex `w` of degree exactly one, and
* every other vertex has degree exactly two.
This breaks the handshake lemma for finite graphs (that there is an even number 
of odd-degree vertices), and so for finite scopes is unsatisfiable.
It is satisfiable for infinite graphs (an infinite ray is an example).

### Monkey Village
Run the following code to compile and run the Monkey Village example.
```
# Compile
javac -cp ".:libs/*" MonkeyVillage.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" MonkeyVillage 2 6 12
```
This example is taken from "Finding Finite Models in Multi-sorted First-Order Logic"
by Reger, Suda, and Voronkov.
To quote their description of the problem:

> Imagine a village of monkeys where each monkey owns at least two bananas.
As the monkeys are well-organised, each tree contains exactly three monkeys.
Monkeys are also very friendly, so they pair up to make sure they will always have a partner.

The numbers provided specify the number of trees, monkeys, and bananas, respectively.
The problem is satisfiable if and only if:
* there are exactly three times as many monkeys as trees,
* there are at least twice as many bananas as monkeys, and
* there is an even number of monkeys.

### SMTLIB Parser/Main

Run the following code to compile and run the Smtlibparsemain example.
```
# Compile
javac -cp ".:libs/*" Smtlibparsemain.java

# Run
java -cp ".:libs/*" -Djava.library.path="libs" Smtlibparsemain x.smt2

This example parses an SMTLIB2 file, turns it into a fortress theory and runs the
default model finder on it with all non-built-in sort scopes set to 10.

