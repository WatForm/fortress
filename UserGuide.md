# Fortress User Guide

Fortress is a Java library for finite model finding (FMF).
It uses many-sorted first-order logic (MSFOL), which is a variation of first-order logic that uses a system of simple sorts (i.e. simple types).
Given an MSFOL theory and sizes for each of its sorts, Fortress answers whether there is an interpretation that satisfies the theory and respects those sizes.

This guide provides an overview of how to create a theory and run a model finder to determine whether the theory is satisfiable or not.  Details on the internal code organization and design decisions can be found in DeverlopersGuide.md .

There are two ways to create an MSFOL theory: from a file or using the fortress API.  Then scopes are added via a model finder and the model finder does the fortress transformations and invokes an SMT solver.

## Creating a MSFOL theory from a file:

inputs.TptpFofParser, inputs.SmtlibParser both make a msfol.theory from a file

Sample use:

    val parser = new SmtLibParser
    val theory = parser.parse(new FileInputStream(inputFilename))

## Creating an MSFOL theory using the fortress API:

There are two steps to creating a theory using the API:
* declare sorts, constants, and functions, and
* add axioms.

Use the following import statements:
```java
import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import java.util.List;
```

We begin with the empty theory:
```java
// Create empty theory
Theory theory = Theory.empty();
```

Next we declare what sorts are in the theory.
First we make sort objects in Java, then add them to the theory.
```java
// Create sort objects
Sort Pigeon = Sort.mkSortConst("Pigeon"); // Pigeons
Sort Hole = Sort.mkSortConst("Hole"); // Holes

// Add sorts to theory
theory = theory.withSorts(Pigeon, Hole);
```

Now we declare what constants and functions are in the theory.
Let's start with the functions.
```java
// Create function declaration objects
FuncDecl holeOf = FuncDecl.mkFuncDecl("holeOf", Pigeon, Hole); // Hole assignment function
FuncDecl isMean = FuncDecl.mkFuncDecl("isMean", P, Sort.Bool()) // Predicate to specify mean pigeons

// Add function declaration to theory
theory = theory.withFunctionDeclarations(holeOf, isMean);
```

Let's do constants next.
First, we make `Var` objects for the constants.
When adding them to the theory, we have to specify the constant's sort.
We do this by annotating the `Var` object with its sort by using the `of` method.

```java
// Create Var objects
Var greg = mkVar("greg"); // Greg the pigeon
Var sue = mkVar("sue"); // Sue the pigeon

// Add constant to theory
theory = theory.withConstants(greg.of(Pigeon), sue.of(Pigeon));
```

With declarations done, we can add axioms.
```java
// Create axiom for "Greg is a mean pigeon and Sue is not a mean igeon"
// In MSFOL this is written as: isMean(greg) and not(isMean(sue))
Term ax1 = mkAnd(mkApp("isMean", greg), mkNot(mkApp("isMean", sue)));

// Add axiom to theory
theory = theory.withAxiom(ax1);
```

When using quantifiers, `Var` objects need to be created for the variables.
Additionally, at the quantification site the `Var` needs to be annotated with its type using the `of` method.
```java
// Create Var objects for quantification
Var h = mkVar("h");
Var p1 = mkVar("p1");
Var p2 = mkVar("p2");
Var p3 = mkVar("p3");

// Create axiom for "Each hole has at most two pigeons"
Term ax2 = mkForall(h.of(Hole),
    mkNot(mkExists(List.of(p1.of(Pigeon), p2.of(Pigeon), p3.of(Pigeon)),
        mkAnd(
            mkEq(mkApp("holeOf", p1), h),
            mkEq(mkApp("holeOf", p2), h),
            mkEq(mkApp("holeOf", p3), h)))));

// Create axiom for "Each mean pigeon has its own hole"
Term ax3 = mkForall(p1.of(Pigeon),
    mkImp( // Implication
        mkApp("isMean", p1),
        mkNot(mkExists(p2.of(Pigeon)),
            mkAnd(
                mkDistinct(p1, p2),
                mkEq(mkApp("holeOf", p1), mkApp("holeOf", p2))))));

// Add axioms to theory
theory = theory
    .withAxiom(ax2)
    .withAxiom(ax3);
```

## Using a Model Finder

With the theory created, we can begin looking for satisfying interpretations.

First we create a `ModelFinder` object.
```java
// Initialize a model finder 
ModelFinder finder = ModelFinder.createDefault();
```

Next we set the `ModelFinder` to use the appropriate theory.
```
// Set the theory of the model finder
finder.setTheory(theory);
```

We now set the *scopes*, which are the domain sizes to use for each sort.
```java
int numPigeons = 10;
int numHoles = 4;

// Set the scopes of the model finder
finder.setAnalysisScope(Pigeon, numPigeons);
finder.setAnalysisScope(Hole, numHoles);
```

Now we can check for satisfiability.
```java
// Check if all axioms in the theory are satisfiable 
ModelFinderResult result = finder.checkSat();

System.out.println("Satisiable?: " + result.toString()); // Will print "Unsat"
```

Different scope sizes may yield different results.

```java
numPigeons = 6;
finder.setAnalysisScope(Pigeon, numPigeons);

ModelFinderResult result = finder.checkSat();

System.out.println("Satisiable?: " + result.toString()); // Will print "Sat"
```

If there is a solution, it can be viewed.
```java
if(result.equals(ModelFinderResult.Sat())) {
    System.out.println(finder.viewModel());
}
```



