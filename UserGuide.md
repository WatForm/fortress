# Fortress User Guide

1. [High Level Overview](#high-level-overview)
2. [Whirlwind Tour](#whirlwind-tour)
3. [Theories in Depth](#theories-in-depth)
    * [Persistence, Immutability, and Equality](#persistence,-immutability,-and-equality)
    * [Typechecking](#typechecking)
    * [Variables, Constants, and Annotations](#variables,-constants,-and-annotations)
    * [Constructing Terms](#constructing-terms)

## High Level Overview
Fortress is a Java library for finite model finding (FMF).
It uses many-sorted first-order logic (MSFOL), which is a variation of first-order logic that uses a system of simple sorts (i.e. simple types).
Given an MSFOL theory and sizes for each of its sorts, Fortress answers whether there is an interpretation that satisfies the theory and respects those sizes.

## Whirlwind Tour
There are two steps to creating a theory:
* declare sorts, constants, and functions, and
* add axioms.

You will want the following import statements:
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

## Theories in Depth

### Persistence, Immutability, and Equality
Theories are immutable and persistent.
Methods like `withAxiom` and `withFunctionDeclarations` don't mutate `Theory` objects - they instead create new `Theory` objects.
If there is a reference to it, the original theory object is still usable.
Consider the following code:
```java
Var p = mkVar("p");
Theory theory1 = Theory.empty().withConstants(p.of(Sort.Bool())).withAxiom(p);
Theory theory2 = theory1.withAxiom(mkNot(p));
```
The `theory2` object contains both the axioms `p` and `mkNot(p)`.
The `theory1` object still exists and contains just the axiom `p`.

Terms similarly are immutable and persistent.
Additionally, they use a natural notion of equality - structurally identical term objects, even if they reside in different locations in memory, are the same.
Consider the following code:
```java
Var p = mkVar("p");
Var p_ = mkVar("p");
Theory theory1 = Theory.empty().withConstants(p.of(Sort.Bool())).withAxiom(p_);
Theory theory2 = Theory.empty().withConstants(mkVar("p").of(Sort.Bool())).withAxiom(p);
```
While `p`, `p_` and `mkVar("p")` might be different Java objects in memory, they can all be used interchangeably and mean the same thing when used to construct terms.
 
### Typechecking
- Only performed when placing axioms within theory

### Variables, Constants, and Annotations
In MSFOL, there is a difference between *constants*, which like functions are declared parts of the theory and accessible in all of the terms, and *variables* which are used for quantification within terms.
Fortress retains this distinction, but to simplify term construction, both are created using `Var` objects.
- Both variables and constants are represented by `Var` objects
- When used in a term, for example as the argument of a function, use their `Var` objects
- Fortress determines whether a given `Var` object is a variable or a constant depending on the context.
If it is enclosed in a quantifier that quantifies over that `Var`, then it is a variable.
Otherwise, it is a constant.
- Shadowing

### Constructing Terms
- list of all term constructors
