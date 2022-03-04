
# Fortress Developer's Guide

This document contains information on how the fortress library is structured and design decisions on its implementation

## Fortress Terminology

* Sorts and constants/functions declared create a `Signature`.  
* `Terms`/formulas are built using the msfol package.  
* A signature and a list of terms together create a `Theory`. 
* A `ProblemState` contains a theory, scopes for the sorts, and additional information that is used throughout the fortress process.
* An `operation` takes a term and applies a transformation to it.
Examples of operations are converting to negation normal form, performing sort inference, simplification, and skolemization.
* A `TheoryTransformer` or `ProblemStateTransformer` takes a `Theory` or `ProblemState` respectively and converts them into a new `Theory` or `ProblemState`by applying a transformation to all terms of the theory (using an operation usually).  Examples of transformers are converting to negation normal form, performing sort inference, simplification, and skolemization.
* Transformations often need to be undone once a solution is found, and so the transformer writes instructions on how to undo its operation on the `ProblemState`.
* A sequence of transformers is combined to create a `Compiler`.  Thus, a compiler takes as input a problem state and produces as output the problem state resulting from the sequence of transformations.
* The compiler also outputs instructions on how to undo all of its transformations to an interpretation.
* A `SolverSession` is an interface to an SMT solver.
* A `ModelFinder` is the top-level interface for fortress used to search for satisfying interpretations to a `Theory` under the given scopes.  Within the model finder, we set the theory, scopes, and other options, and we can invoke its solving methods.

## Basic Algorithm of Fortress

Two problems are "equivalent" when every interpretation satisfies one if and only if it satisfies the other.
In order for two problems to be equivalent, they must have the same signature (otherwise it doesn't make sense to evaluate them using the same interpretation).

Two problems are "equisatisfiable" when the answer to the question of their satisfiability is the same: that is, either both are SAT or both are UNSAT.
Equivalent problems are always equisatisfiable, but equisatisfiable problems need not be equivalent.
Equisatisfiable problems do not need to have the same signature; the only thing that matters is the answer to their satisfiability questions is the same.

The "unbounded" version of problem is the problem obtained by removing the scopes on any bound sorts.

A problem is "formulaically bound" if the following condition holds: the only interpretations that satisfy the unbounded version of the problem are those that satisfy the original (bounded) version.
If a problem is formulaically bound, it is equisatisfiable with its unbounded version.

The basic algorithm that Fortress implements consists of the following steps.


1. Negation Normal Form (NNF): The formulas of the problem are transformed into negation normal form, where negations are pushed down as far as possible into the formulas. The resulting problem is equivalent to the first.

2. Skolemization: Existential quantifiers are eliminated by replacing them with functions and constants that act as witnesses for the existential quantifiers.
The signature is changed by the introduction of new functions and constants.
This operation must be performed after putting formulas into negation normal form, as otherwise it is impossible to tell which quantifiers are truly existential (since negations change quantifiers).
Given this condition however, the resulting problem is equisatisfiable to the input problem.

3. Symmetry Breaking: Additional constraints are added to reduce the number of interpretations that need to be checked by the solver.
The resulting problem is equisatisfiable to the input to this step.

4. Universal Quantifier Expansion: Universal quantifiers of bounded sorts are expanded by taking each possible instantiation and then taking their conjunction.
The resulting problem is equivalent to the input to this step.

5. Simplification: The formulas are simplified as much as possible.
The resulting problem is equivalent to the input to this step.

6. Range Formulas: Range formulas are introduced, which use the scopes to explicitly list the possible output values of each function and constant.
These range formulas are quantifier-free, so as to not introduce any more quantifiers after universal expansion.
The resulting problem is both equisatisfiable to the input to this step and *formulaically bound*.

7. Domain Elimination: Constants are introduced to "simulate" the domain elements.
Specifically, for each domain element in the problem, a unique constant is generated.
It is asserted that these constants are mutually distinct from each other.
The domain elements are then replaced with their respective constants.
The resulting problem is equisatisfiable to the input to this step, and contains no domain elements.
This operation also maintains the property of being formulaically bound. 

8. Scope Removal and SMT Invocation: The unbounded version of this final problem is converted into a format that is accepted by an SMT solver (the problem contains no domain elements, so this can be done).
The SMT solver is then invoked.
Whatever result the solver returns is then returned to the user.


All that Fortress needs to guarantee is that after its transformations, the final problem is equisatisfiable to the first input problem.

After applying the above transformations, the final problem is:
* equisatisfiable to the original problem, and
* formulaically bound (so its scopes can be removed).

Therefore, removing the scopes still leaves a problem equisatisfiable to the original, and, provided the SMT solver gives a correct result, so too does Fortress.

If the original problem gives a scope for every sort, then because of the universal expansion step, there are no quantifiers in the final unbounded problem sent to the SMT solver.
Such problems fall under the fragment of first-order logic called the logic of equality with uninterpreted functions (EUF), which is decidable.
In SMT literature, this logic is called the logic of quantifier-free uninterpreted functions (QF_UF).
SMT solvers are decision procedures for such problems, and therefore so too is Fortress.

The fortress library includes a number of options for the above steps.

## Fortress Architecture and Design Decisions

The following refer to the packages that are part of Fortress.

### msfol
* Methods to create sorts, constants, functions (including built-ins), terms, and theories.  
* a signature is created using 'with' methods in Signature.scala
* Names.scala checks for illegal names
* In MSFOL, there is a difference between *constants*, which like functions are declared parts of the theory and accessible in all of the terms, and *variables* which are used for quantification within terms. Fortress retains this distinction, but to simplify term construction, both are created using `Var` objects.
    + Both variables and constants are represented by `Var` objects
    + When used in a term, for example as the argument of a function, use their `Var` objects
    + Fortress determines whether a given `Var` object is a variable or a constant depending on the context.
    + If it is enclosed in a quantifier that quantifies over that `Var`, then it is a variable.
    + Otherwise, it is a constant.
* terms are created using the methods in Term.scala:
    - EnumValue is a kind of term. DomainElement is also a kind of term.   
    - To create a quantified variable use mkVar(x).of(Sort); this is not a term, it is an AnnotatedVar(Declaration), which can be passed as an argument to create a quantified term.
    - All have toString methods defined.  
    - Sorts are not stored in terms except for sorts of quantified variables.
* DSL.scala is a small DSL for MSFOL to help write terms rather than going through Term interface always.  @TBA: where are some examples of the use of this DSL.
* @TBA: something about explicit/implicit caching
* TermVisitor.scala is a trait for walking of terms that is parameterized by the return type.
* typechecking is only performed when placing axioms within theory for efficiency (reduces the number of times a term is typechecked)
* Theories are immutable and persistent.
    - Methods like `withAxiom` and `withFunctionDeclarations` don't mutate `Theory` objects - they instead create new `Theory` objects.
    - If there is a reference to it, the original theory object is still usable.
    Consider the following code:
```java
Var p = mkVar("p");
Theory theory1 = Theory.empty().withConstants(p.of(Sort.Bool())).withAxiom(p);
Theory theory2 = theory1.withAxiom(mkNot(p));
```
The `theory2` object contains both the axioms `p` and `mkNot(p)`.
The `theory1` object still exists and contains just the axiom `p`.

    - Terms similarly are immutable and persistent.
    - Additionally, they use a natural notion of equality - structurally identical term objects, even if they reside in different locations in memory, are the same.
Consider the following code:
```java
Var p = mkVar("p");
Var p_ = mkVar("p");
Theory theory1 = Theory.empty().withConstants(p.of(Sort.Bool())).withAxiom(p_);
Theory theory2 = Theory.empty().withConstants(mkVar("p").of(Sort.Bool())).withAxiom(p);
```
While `p`, `p_` and `mkVar("p")` might be different Java objects in memory, they can all be used interchangeably and mean the same thing when used to construct terms.

### inputs
* This is the code that maps TPTP or SMT-LIB files into a theory.  This code is in java (rather than scala).
* TheoryParser: the general class for parsing a file into a theory.
    - TptpFofParser 
        + an instance of a TheoryParser for TPTP
        + relies on TptpToFortress (visitors over the antlr grammar for TPTP to produce a theory; formulas, fcn declarations, and prime propositions are collected separately and then added to the theory after visiting the file.
        + TPTP files are unsorted so only the universeSort is used. The universeSort is not built-in.  It is declared as a sort constant. 
        + Not yet supported: infix <~> for non-equivalence(XOR),  infix ~| for negated disjunction (NOR), infix ~& for negated conjunction (NAND) 
    - SmtLibParser
        + an instances of a TheoryParser for SMT-LIB
        + relies on SmtLibVisitor to convert the parsed data into a theory using visitors over the antlr grammar for SMT-LIB. 
        + info and logic from the SMT-LIB parser are not used further in Fortress. 
        + Bool and Int sorts are mapped to Fortress' built-in Bool and Int sorts. 
        + Let statements (parallel substitution) are substituted to create terms. 
        + Ignores check-sat commands.  
        + Not yet supported: Right/Left bitshift, unsigned div/rem, and, or, not, concat bit operations; abs val for ints.  

### antlr
* FOFTPTP.g4 - parses TPTP
* SmtLibSubset.g4 - parses SMT-LIB @joe is this SMT-LIB2?

### Sortinference
* Functions for performing sort inference

### operations
* Operations apply to terms. To apply an operation to a term/theory using "wrap" as in 
```
operation.wrapTerm(t:term)
operation.wrapTheory(t:theory)
```
* Examples of operations
    - ClosureEliminator: under development for transitive closure
    - DeBruijnConverter: converts a term to a term with DeBruijn var # (rather than names) 
    - InterpretationVerifier: verifies that an interpretation satisfies a theory.
    - NormalForms: converts a theory/term to nnf; conversion to prenex normal form is not yet implemented.
    - QuantifierExpander/QuantifierExpanderSimplifier
        + expands the quantifiers to And/Or using sort values
        + in the Simplifier one, the simplifier is called on each expansion.
    - RecursiveEliminators
        + replaces enumvalues/domain elements in terms with constants.
    - Simplification/Simplification2/SimplificationWithLearnedLiterals
        + some simple simplifications (not true == false, two domain elements are not equal) 
        + Without the simplification step, Z3 takes a significantly longer time to run.
    - SimplificationWithRange
        + like the previous operation, but range restrictions are passed as an argument and used to simplify formulas. 
    - Skolemizer
        + skolemizes a term, which produces a new term, skolem constants and functions.
     - SmtlibConversion
        +  converts a term to the strings needed for SMT-LIB. 
        +  We add suffixes "aa" to all variable and function names when converting to SMT-LIB to avoid having reserved keywords as identifiers. And when reading the results, we remove all the suffixes added.
    - Substitution
        + substitutes a term for a variable in a term.  Performs needed alpha-renaming to avoid variable capture. 
        + FastSubstitutor does a bunch of substitutions in parallel.
    - TermConvertor
        + Converts Ints to Signed Bit Vector operations. 
    - TermMetrics: 
        + various metrics on terms (depth of quantification, depth of nested functions, number of nodes in a term)
    - TermVisitorWithTypeContext/TypeChecker
        + typechecks a term.  
        + Builds the context of quantified variables and their types.  
        + All primitive term parts (constants, variables, function declarations are explicitly typed) sorted so there is no type inference here.
* Some helper code:
    - RecursiveAccumulator
        + functions that collect things like free variables, domain elements, constants, functions in a term.
    - RecursivePatterns:
        + apply a function recursively over terms.     

### transformers
* All the operations that transform a theory or a problem state. 
* contains ProblemStateTransformers and TheoryTransformers 
* `apply` method 
    - takes a theory and creates a problem state
    - takes a theory and scopes and creates a problem state
    - takes a problem state and produces a problem state
- `asProblemStateTransformer` for a theoryTransformer it into a problem state transformer
* With respect to efficiency, each transformer may walk over the entire theory.  After quantifier expansion, theories can be quite large and in the future, we may wish to integrate some transformers for efficiency.
* mostly the list of transformers matches the list of operations with the following additions:
    - DomainEliminationTransformer:
    - EnumEliminationTransformer: replace enum elements with constants; assert these constants are distinct
    - IntegerFinitization: under development
    - RangeFormulaTransformer/RangeFormulaTransformer_NoElision: adds range formulas
    - SortInferenceTransformer: infers new sort; adds these sorts; unapply reverses the sort substitution
    - SymmetryBreaking: adds symmetry breaking constraints to the theory

### symmetry
* code for adding symmetry breaking
* a number of symmetry breaking schemes are implemented
* Code could probably be simplified

### compiler
A packaging mechanism for a sequence of transformations.
* LogicCompiler 
    - The "compile" method takes a theory and scopes, and returns either CompilerError of CompilerResult (theory,decompileInterpretation,skipForNextInterpretation )
* TransformationCompiler 
    - The "compile" method builds a problem state and applies transformers.
* BaseFortressCompiler 
    - Defines the transformer sequence usually applied, parameterized by symmetry breaking transformers.
* FortressCompilers: Define the fortress compilers (Zero, ONE, etc) as the BaseFortressCompilers plus certain symmetry breaking.

### solverinterface
* These are ways of connecting to external solvers.  
* Main methods are:
1) setTheory - takes a theory (returns Unit)
2) addAxiom - takes an axiom and adds it to the theory (returns Unit)
3) solve - take a timeout value and returns a ModelFinderResult
4) solution - returns the interpretation from the solver
* Fortress has a general SolverSession interface
* We found that using the term building (API) interfaces of SMT solvers was very slow.  Our best guess is that this is because the Z3 API performs some kind of typechecking when expressions are constructed, so recursively building terms bottom-up repeatedly invokes the typechecker at each expression construction, greatly slowing the process.
* So now fortress converts a theory to a string in SMT-LIB and this can be passed to any SMT-LIB solver.  
* We use Java'a ProcessBuilder class to manage an interactive session with the solver.  
* Currently we support Z3 and CVC4 and we map the returned instance back to fortress interpretations (ProcessSmtlibEvaluation).  
* Interaction with the incremental solver via the process builder has not been well tested. 
* SolverInterface: The main interface to the solvers implemented - creates sessions with particular solvers.
* Code could probably be simplified
* Seemingly innocuous name changes can have unexpected performance consequences.
For example, changing the prefix used for domain constants from `@` to `%` (in order to be more compliant with the standards used by SMT solvers) caused performance in some tests to slow down, at least when using the Z3 Java API.
Changing it to `_@` (also standards-compliant) improved performance again.

### modelfind
* ModelFinder is the main fortress interface.  
* A model finder takes a solver and a theory as arguments and performs solving on the theory returning a result (and an interpretation when appropriate).
* important methods:
1) setTheory(theory: Theory): Unit
2) setAnalysisScope(t: Sort, size: Int): Unit
3) setTimeout(milliseconds: Int): Unit
4) setBoundedIntegers(semantics: IntegerSemantics): Unit
5) checkSat(): ModelFinderResult
6) viewModel(): Interpretation
7) nextInterpretation(): ModelFinderResult
8) countValidModels(newTheory: Theory): Int
* Integer semantics can be: UnboundedSemantics, ModularSignedSemantics(bitwidth: Int)
* The default ModelFinder is FortressZero.
* The main ModelFinders defined (which depend on certain Compilers chosen):
- FortressZERO - no symmetry breaking
- FortressONE - Claessen and Sorensson symmetry breaking only
- FortressTWO - functions first for symmetry breaking
- FortressTWO_SI - sort inference then functions first for symmetry breaking
- FortressTHREE - 
- FortressTHREE_SI
- FortressFOUR_SI

### interpretation
* data structures for representing the interpretation returned by a solver.
* Interpretation
    - includes maps for sorts, constants, and functions.  
    - can be turned into a String or turned into constraints

### data
* Useful data structures/functions for fortress such as UnionFind, Caching

### util
* Functions for timers, errors, lists, maps.
* Notably ArgumentListGenerator.scala relies on msfol._ and data._

### logging
* EventLogging is the main trait with different classes for recording timing for various processes.




















