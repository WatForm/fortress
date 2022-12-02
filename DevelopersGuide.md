# Fortress Developer's Guide

This document contains information on how the Fortress library is structured and design decisions in its implementation.

## Fortress Terminology

* Sorts and constants/functions declared create a `Signature`.  
* `Terms`/formulas are built using the msfol package.  
* A signature and a list of terms together create a `Theory`. 
* A `ProblemState` contains
    - a theory 
    - scopes for the sorts
    - unapply (see below)
    - rangeRestricts (where added? symmetry and range formulas - duplicate info?)
    - anything else?
* Elements of a bounded sort are called `domain elements`.
* A sort scope can be 
    - `unbound` or `bound` (with a scope size)=
    - `exact` or `inexact`
    - `changeable` or `unchangeable` (once)
* An `operation` takes a term and applies a transformation to it.
Examples of operations are converting to negation normal form, performing sort inference, simplification, and skolemization.
* A `TheoryTransformer` or `ProblemStateTransformer` takes a `Theory` or `ProblemState` respectively and converts them into a new `Theory` or `ProblemState`by applying a transformation to all terms of the theory (using an operation usually).  Examples of transformers are converting to negation normal form, performing sort inference, symmetry breaking, adding range formulas.
* Transformations often need to be undone once a solution is found, and so the transformer writes instructions (called `unapply`) in the problem state on how to undo its operation on an interpretation of the ProblemState to make it understandable to the user in terms of the original theory.
* A sequence of transformers is combined to create a `Compiler`.  Thus, a compiler takes as input a problem state and produces as output the problem state resulting from the sequence of transformations.
* The compiler also outputs instructions on how to undo all of its transformations to an interpretation.
* A `SolverSession` is an interface to an SMT solver.
* A `ModelFinder` is the top-level interface for fortress used to search for satisfying interpretations to a `ProblemState`.  Within the model finder, we set the theory, scopes, and other options, and we can invoke its solving methods.

## Basic Algorithms of Fortress

Fortress applies a ModelFinder to an problem state.  The steps of a model finder are: 1) apply a compiler (a sequence of transformers) and 2) convert the problem to SMT-LIB and pass the problem to a solver.  Alternatively, it can use the API of an SMT solver directly.

There are three standard model finders available in Fortress, which differ in the compiler used.  In all existing model finders, the non-incremental Z3 solver is used.

1. Constants Method

This is the method described in the original paper on Fortress where a finite set of distinct constants (called domain elements) are created to represent the values of elements in the sort, quantifier expansion is done over these domain elements and every function application/constant in the theory is constrained to return a value of the sort (these constraints are called range formulas).  To optimize the resulting problem for solving, simplication and symmetry reduction axioms are included as transformers.  This method results in a theory in EUF - a decidable subset of FOL, which is passed to the solver.

2. Datatype Method

SMT solvers provide datatypes declarations where the values of a sort can be enumerated.  In this method, datatype values are created for domain values.  Range axioms are not needed.  Symmetry reduction axioms are added.
* __is quantifier expansion needed__?
* __is it decidable__

3. Minimal Method

In this method, only typechecking is done so that the SMT solver can work with the problem directly. The problem may not be decidable.

Please see the code for the sequence of transformers used for each method 
above.

There are also a number of experimental model finders present in the code that implement various forms of symmetry breaking in the constants method:
    + FortressZERO - no symmetry breaking
    + FortressONE - Claessen and Sorensson symmetry breaking only
    + FortressTWO - functions first for symmetry breaking
    + FortressTWO_SI - sort inference then functions first for symmetry breaking
    + FortressTHREE - Claessen and Sorensson, RDI, RDD, ladder
    + FortressTHREE_SI - sort inference then Claessen and Sorensson, RDI, RDD, ladder
    + FortressFOUR_SI - trial of adding heuristics to fortress three si


## Attributes of problemState

* typechecked 
    - boolean within problemState
* defn 
    - there are definitions in the theory
    - can check in theory
    - it's possible to have in input theory
* nnf 
    - boolean within problemState
* onlyForall 
    - the axioms of the theory contain only universal quantifiers
    - boolean within problemState
* noQuant
    - the axioms of the theory contain no quantifiers 
    - boolean within problemState
* decidable 
    - the axioms of the theory are within a decidable subset of predicate logic
    - boolean within problemState
* unbounded 
    - there are unbounded sorts in the problemSate
    - can check in sorts of problemState
* int
    - the built-in IntSort is used in the theory 
    - boolean within problemState
* tc 
    - transitive closure is used in the axioms of the theory
    - boolean within problemState)
* exactScope 
    - all scopes are finite and exact
    - boolean within problemState
* enum
    - contains enums 
    - can we check this in the theory? 
* de 
    - where are these stores?
    - can we check this within the theory?
* datatype 
    - possible to have in input theory
    - can we check this in the theory?

Anything that changes the scopes needs to be noted.

We use !attribute to mean not having the attribute as in !nnf.

If an attribute of the problemState is not mentioned below when describing
the transformers, then its value does not change

Modifies can contain: theory (signature, axioms), problemState (scopes, rangeRestricts, unapply)

## Transformers

Below is a brief description of the transformers implemented in Fortress. 
Some transformers below are for experimentation and thus not used in 

* TypecheckSanitizeTransformer @Nancy
    - theory -> theory
    - no change in theory
    - purpose: 
        + performs typechecking (no type inference) on theory
        + can handle defns
        + what does it return if it fails?
        + replace instances of Eq with Iff
 * when comparing Bool sort
    - methods: all
    - preconditions: none
    - modifies: axioms
    - postconditions: typechecked
    - unapply: none
    
* ScopesNonExactPredicatesTransformer @Xintong
    - problemState -> problemState
    - purpose: set up predicates for non-exact scopes
    - methods: constants, datatype
    - preconditions: typechecked
    - modifies: scopes
    - postconditions: exactScopes
    - unapply: ???

* EnumEliminationTransformer @Nancy
    - problemState -> problemState
    - purpose: 
        - enums become domain elements (?)
    - methods: all
    - preconditions: typechecked
    - modifies: signature
    - postconditions: !enum 
    - unapply: Enums (?)


* AxiomatizeDefinitionsTransformer @Xintong
    - theory -> theory
    - purpose: 
        + turn the defns into axioms and defn names become uninterpreted functions
    - methods: constants, datatype
    - preconditions: typechecked
    - modifies: signature? adds axioms
    - postcondition: !defns
    - unapply: none
    
* Handling Integers (use one of these) @Owen
    - IntegerToBitVectors 
        + problemState -> problemState
        + purpose: 
            * Turn integer sorts into twos complement BVs based on bitwidth ??
            * no change to formulas
            * removes IntSort from sorts
        + preconditions: typechecked
        + postconditions: !ints
        + unapply: ??
    - NoOverflow 
        + problemState -> problemState
        + purpose: 
            * Turn integer sorts into twos complement BVs based on bitwidth ??
            * converts formulas for Alloy no overflow semantics 
            * removes IntSort from sorts
        + methods: constants, datatype
        + preconditions: typechecked
        + postconditions: !ints
        + unapply: ??
        

* Transitive Closure (use one of these) @Owen
    - ClosureNegativeTransformer 
        + problemState -> problemState
        + purpose: 
            * if the tc of an expr is only uses positively
            * replaces the tc with a new, uninterpreted, axiomatixed function
            * may still be negative uses of tc remaining
        + methods: constants, datatype, minimal
        + preconditions: nnf, typechecked
        + postconditions: !nnf, !skolemized, !noQuant, !onlyForall
        + unapply: removes all functions it created from the interpretation

    - ClosureEliminationEijckTransformer
    - ClosureEliminationLiuTransformer
    - ClosureEliminationClaessenTransformer
        + problemState -> problemState
        + purpose: 
            * remove all uses of transitive closure
            * replaces the tc with a new, uninterpreted, axiomatized function
        + methods: constants, datatype, minimal
        + preconditions: typechecked
        + postconditions: !tc, !nnf, !skolemized, !noQuant, !onlyForall
        + unapply: removes all functions it created from the interpretation
    
* SortInferenceTransformer    @Nancy    
    - theory -> theory
    - purpose: 
        + infer sorts for more symmetry SymmetryBreaking
    - methods: constants, datatype
    - preconditions: typechecked, !defns
    - modifies: 
        + add newly found sorts to signature 
        + changes types of constants/functions in signature 
        + modifies axioms with new sorts
    - postconditions: no change
    - unapply: ??


* NnfTransformer @Xintong
    - theory -> theory
    - purpose: put all axioms in nnf
    - methods: constants, datatype
    - preconditions: nodefs, typechecked
    - modifies:
    - postconditions: nnf
    - unapply: ??

* PnfTransformer (not yet written)
    - not yet implemented

* SkolemizeTransformer @Xintong
    - theory -> theory
    - purpose: 
        + skolemize all axioms
        + skolem constants/functions are added to the signature
    - methods: constants, datatype
    - preconditions: nodefs, typechecked, nnf
    - postconditions: onlyForall
    - postconditions: nodefs, typechecked, nnf, onlyForall
    - unapply: nodefs, typechecked, nnf, onlyForall


* Symmetry @Nancy
    - SymmetryBreakingMonoOnlyAnyOrder
    - SymmetryBreakingFunctionsFirstAnyOrder
    - SymmetryBreakingMonoFirstThenFunctionsFirstAnyOrder
    - SymmetryBreakingLowArityFirstMostUsedFunctionFirstOrderFactory
            * symmetry axioms are quantifier-free

* StandardQuantifierExpansionTransformer @Nancy
    - purpose:
        + remove all universal quantifiers
        + replace with the conjunction of the substitution all domain element values
        + all bound scopes become unchangeable
    - methods: constants
    - preconditions: onlyForall, !defn, typechecked
    - modifies: axioms
    - postcondition: !quantifiers
    - unapply: none

* RangeFormulas @Nancy
    - RangeFormulaStandardTransformer 
        + purpose: 
            * introduce range formulas using domain elements to axioms
            * if not already limited by symmetry breaking
            * all bound scopes become unchangeable
            * range formulas are quantifier-free
        + methods: constants
        + preconditions:
        + modifies: axioms, scopes
        + postconditions: de
        + unapply: ?
    - RangeFormulaUseConstantsTransformer 
        + purpose
            * introduce range formulas using constants 
            * if not already limited by symmetry breaking)  
            * all bound scopes become unchangeable      |


* Simplify @Owen
    - Note: most of these likely can be combined. Simplifiers for specific methods just won't simplify for others.
    - Note: None of these unapply
    - Note: It is probably best to use these after adding range restrictions and quantifier expansion (second to last transformer).
    - SimplifyTransformer 
        + Purpose
            * Reduces double negations and negation of Boolean constants
            * Simplify `AndList` and `OrList` containing Boolean constants
            * Simplify `Implication` and `Iff` s containing Boolean constants
            * Simplify `Eq` of domain elements
            * Simplify `Eq` of the same variable (`Eq(Var('x'), Var('x'))`) or where they have different interpretations
            * Simplify `Eq` with identical content
            * Simplifies `Exists` and `Forall` to remove unused variables
            * Simplifies `ITE` with known condition
        + methods: any
        + preconditions: none
        + postconditions: none 
    - SplitConjunctionTransformer
        + Purpose
            * Splits all top-level conjunct formulas into separate formulas
        + methods: any
        + preconditions: none
        + postconditions: none
    - SimplifyLearnedLiteralsTransformer
        + Purpose
            * Same as `SimplifyTransformer` unless otherwise stated
            * Replaces subterms with any learned literal during the simplification process
        + methods: any
        + preconditions: none
        + postconditions: none
    - SimplifyTransfomer2
        + Purpose
            * Same as `SimplifyTransformer` unless otherwise stated
            * Only checks `Eq` for left and right being equal
        + methods: any
        + preconditions: none
        + postconditions: none
    - SimplifyWithRangeTransformer
        + Purpose
            * Same as `SimplifyTransformer` unless otherwise stated
            * Uses range restrictions to check if equality between a term and a domain element is impossible
        + methods: any
        + preconditions: none
        + postconditions: none

    
* DomainElimination @Owen
    - DomainEliminationTransformer 
        + purpose: 
            * add constant to theory for each domain element
            * add axiom that these constants are mutually distinct
            * replace DEs with constants
            * remove DEs from theory (?)
        + methods: constants
        + preconditions: !tc, !ints ...
        + postconditions: !de, euf
    - DomainEliminationTransformer2
        + non-exact scopes by non-distinct constants - to remove       |
    - DatatypeTransformer 
        + purpose: 
            * replace DEs with datatypes
            * adds datatype definition to theory
        + methods: datatypes

## Solvers

* non-incremental Z3 session
* CVC5 session
* Z3 API


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
* Enums are constants in MSFOL that are distinct and cover all possible elements of the sort. They are distinct from domain elements (also a kind of term), which are the values of the sorts used internally in fortress.  Not all sorts have enums, but all sorts have domain elements for FMF.  Domain elements are used to create range formulas.  Enums are converted to domain elements by a transformer (below).  The DomainEliminationTransformer (below) is the last step in fortress to convert all domain elements to mutually distinct constants so that the problem can be solved by an MSFOL solver.
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
    - Defines the SimpleModelFinder which exposes the compiler and interface to direct control from the user

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




















