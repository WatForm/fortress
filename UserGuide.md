# Fortress User Guide

This guide is intended to provide an overview of how to create a theory and run a model finder to determine whether the theory is satisfiable or not.  Details on the internal code organization and design decisions can be found in DeverlopersGuide.md .

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





### Step 1: Ways to make a MSFOL theory

a) You can make a MSFOL theory from a file:

inputs.TptpFofParser, inputs.SmtlibParser both make a msfol.theory from a file

Sample use:

    val parser = new SmtLibParser
    val theory = parser.parse(new FileInputStream(inputFilename))

b) You can make a MSFOL theory through the API:

msfol.Sort (mkSortConst+builtin sorts constructor) 
+ msfol.Declaration (mkFcnDecl constructor)              
+ msfol.Declaration (AnnotatedVar constructor creates a constants)
together make a msfol.signature

msfol.signature
+ axioms (terms of Bool sort)
together make a msfol.theory. Axioms are constructed via ms.term.

Sample use:
    val A = Sort.mkSortConst("A")
    val c = Var("c").of(A)
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)
    val term1 = Forall(x.of(Sort.Bool), Or(x, App("P", x)))
    val term2 = Not(App("P",c))
    val sig = Signature.empty
                .withSorts(A)
                .withConstants(c)
                .withFunctionDeclarations(P)
                .withAxioms(term1,term2)

Enums are constants in MSFOL that are distinct and cover all possible elements of the sort. They are distinct from domain elements (also a kind of term), which are the values of the sorts used internally in fortress.  Not all sorts have enums, but all sorts have domain elements for FMF.  Domain elements are used to create range formulas.  Enums are converted to domain elements by a transformer (below).  The DomainEliminationTransformer (below) is the last step in fortress to convert all domain elements to mutually distinct constants so that the problem can be solved by an MSFOL solver.

There is also a DSL that can be used to create terms in a less cumbersome way than the term API directly.

Sample usage:
@Joe - where can I find an example of the use of this DSL?

### Step 3: Ways to solve the theory

The solvers use an external solver package to solve a MSFOL theory. For a FMF problem, the scopes are expected to be used in the transformation of an MSFOL theory to another MSFOL theory prior to solving.  The encorporation of the scopes into the MSFOL theory (via range formulas) means the theory only finite solutions of the expected scopes, thus scopes are not needed by the solver interface.

A sample interaction with a solver (in scala) is:

    // Open new solver session
    val session = Z3IncCliInterface.openSession()
    // Convert to solver format  @Joe ????
    session.setTheory(finalTheory)
    // Solve
    session.solve(maxTimeMillis)
    // s is a ModelFinderResult (one of Sat,Unsat,Unknown,Timeout)
    s = session.checkSat()
    // get a satisfying Interpretation
    var i1 = session.viewModel()
    // get the next satisfying Interpretation
    var i2 = session.nextInterpretation() 
    // close the session
    session.close()

Other solver interfaces are:
Z3CliInterface
CVC4CliInterface  

There is additional logging/timing that can be added to the above session.

### ModelFinders (a package of the above three steps)

A ModelFinder packages up the above three steps. It takes a FMF problem (theory and scopes);transforms the problem using a compiler; and solves the problem using a solver interface. The results of solving are available via the "checkSat" and "viewModel" methods. The methods nextInterpretation/countValidModels are also useful.  A ModelFinder is parameterized by IntegerSemantics.  Different model finders are defined in FortressModelFinders.  These use the Z3 Incremental solver by default.  Details regarding wrapping the theory into a problem state are hidden in a model finder.

The following code (in scala) shows a sample usage of a ModelFinder:

    val modelFinder = new FortressTHREE_SI

    // create the theory
    val parser = new SmtLibParser
    val theory = parser.parse(new FileInputStream(inputFilename))
    modelFinder.setTheory(theory)

    // Default scope to be used for all sorts
    val defaultScope = 10
    for((sort, scope) <- scopes) {
        modelFinder.setAnalysisScope(sort, defaultScope)
    }

    // maximum time for the ModelFinder to run
    val timeout = 15*60*1000  // 15 minutes in seconds
    modelFinder.setTimeout(Seconds(timeout))

    // integers will have unbounded semantics
    // meaning Ints in the theory map to Ints in SMT-LIB
    val integerSemantics = Unbounded
    modelFinder.setBoundedIntegers(integerSemantics)

    // solve
    val result = modelFinder.checkSat()
    println(result)
    if(conf.generate()) {
        result match {
            case SatResult => println(modelFinder.viewModel())
            case _ => { }
        }
    }
    // @Joe let's add something to check the correctness of the result

