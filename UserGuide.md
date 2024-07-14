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

## Using smttc

`.smttc` is an extension to the `.smt2` file format that includes Fortress features.

### Transitive Closure

The most notable feature included in `.smttc` is transitive closure. 
Transitive closure expressions are written as `(closure R x y [fixedargs...])` or `(reflexive-closure R x y [fixedargs...])` for reflexive closure.

The term `(closure R start end)` evaluates to true if there is an edge from `start` to `end` in the transitive closure of `R`.
`R` should be the identifier for the relation to be closed over. `start` and `end` are terms.

Fortress also supports transitive closure over relations of higher airity.
Consider `R: A x A x B x C`. One can write `(closure R start end fixB fixC)` where `fixB` is a term of sort `B` and `fixC` is a term of sort `C`.
The closure then works as above over the relation `R'` where `(start, end) \in R'` if and only if `(start, end, fixB, fixC) \in R`.

### Scope Information

Fortress supports three `set-info` keywords for setting scope information from a `.smttc` file:
- `:exact-scope` is used to set exact scopes
- `:nonexact-scope` is used to set non-exact scopes
- `:unchanging-scope` is used to specify which sorts Fortress is not allowed to change

Each of these keywords expect a string value. The `exact` and `nonexact` scope methods expect a series of optionally whitespace separated `(sort scope)` specifiers. Sort must be an identifier and scope must be an integer. There must be at least some amount of whitespace separating the sort and scope.

The specifier for unchanging scopes expects a series of `(sort)`s optionally separated by whitespace.

For example:
```smt2
(set-info :exact-scope "(A 1) (|Complicated Name!!| 3)")
(set-info :nonexact-scope "(B 2)")
(set-info :unchanging-scope "(A)(|Complicated Name!!|)")
```



