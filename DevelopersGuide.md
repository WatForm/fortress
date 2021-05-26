# Fortress Architecture and Usage

This is a guide for fortress users and developers.  All sample uses are in scala, but could be written in Java.
Following the Overview sections, the packages are described in bottom-up order.

@Joe 
    - below takes the place of the fortress TR that I had planned so have archived that folder
    - it would be good to document design decisions below also

## Overview
@Joe - I'd like this overview to not use fancy scala features, rather language constructs that most would understand.

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

## data 
Useful data structures/functions for fortress such as UnionFind, Caching,
@Joe - the typechecking exceptions here seem oddly located

## util 
Functions for timers, errors, lists, maps.
Notably ArgumentListGenerator.scala relies on msfol._ and data._

## msfol 
Ways to create Sorts, constants, functions, terms.  All have toString methods defined.  Sorts are not stored in terms except for sorts of quantified variables.  

### Names.scala
Object to store/test for illegal names

### Sort.scala
Sort class
attributes: name, isBuiltin, toString
constructors:
- mkSortConst(name)
- Bool
- Int  
- BitVectorSort(bitwidth:Int)

### Declarations.scala
Declaration class (for function declarations)
attributes: arity, isRDD,isRDI,isMonoSorted,isRainbowSorted
constructors: 
- mkFuncDecl(name,argsortsList,resultsort) 
- AnnotatedVar(var+sort for quantified variables, is a declaration not a term)
- apply(var,arg1,arg2,...,resultsort)
- mkFuncDecl(var,arg1,arg2,...,resultsort)
@Joe - why have both apply and mkFuncDecl with variable # of args?

### BuiltinFunctions.scala
- BuiltinFunctions trait 
- integer/bv functions

### DSL.scala
- small DSL for MSFOL to help write terms rather than going through Term interface always

### RangeRestriction.scala
A term that is equivalent to saying a term equals one of a set of domain elements.

### Term.scala
Constructors for creating a term.  In addition to the usual terms, EnumValue is a kind of term. DomainElement is also a kind of term.   To create a quantified variable use mkVar(x).of(Sort); this is not a term, it is an AnnotatedVar(Declaration).

@Joe - we need something here to describe the explicit caching that is done (for domain elements and fcn applications) and a hint about the implicit caching that is done by the scala compiler.

### TermVisitor.scala
Trait for Visitor for walking over terms - parameterized by return type.

### Signature.scala
Attributes: set of sorts, set of funcDecls, set of constants, set of enumConst
Methods: 
- withSort, withSorts, etc (varying number of args)
Includes function replaceIntegersWithBitVectors (just in signature).
Does consistency checking for signature as items are added.

### Theory.scala
Attributes:
- signature
- axioms
Provides similar methods to signature
Constructors:
- empty
- mkTheoryWithSignature
- with's for adding axioms

### TypeCheckTraits.scala
@Joe - could this be just added to the signature?

## inputs 
This is the code that maps TPTP or SMT-LIB files
into a theory.  This code is in java (rather than scala).
Hierarchy:
- TheoryParser: the general class for parsing a file into a theory.
    - TptpFofParser: Is an instance of a TheoryParser for TPTP; relies on TptpToFortress to map the parsed data into a theory. Note that Tptp files are unsorted so only the universeSort is used. The universeSort is not built-in.  It is declared as a sort constant.  Returns a theory. In TptpToFortress, visitors over the antlr grammar for TPTP to produce a theory. Formulas, fcn declarations, and prime propositions are collected separately and then added to the theory after visiting the file.
    - SmtLibParser: Is an instances of a TheoryParser for SMT-LIB; relies on SmtLibVisitor to convert the parsed data into a theory. Returns a theory.  Also includes info and logic from the SMT-LIB parser, but these are not used further in Fortress. SmtLibVisitor has visitors over the antlr grammar for SMT-LIB.  Maps Bool and Int sorts to Fortress' built-in Bool and Int sorts.  Theory is built directly during the visitor.  Let statements (parallel substitution) are substituted to create terms.  Attributes in SMT-LIB are ignored. Ignores check-sat commands.  Not yet supported: Right/Left bitshift, unsigned div/rem, and, or, not, concat bit operations; abs val for ints.  
    @Joe: it would be good to fix the SmtLib files/parsers to use the same naming conventions - one is called a Visitor and one is called ToFortress.
    @Joe - the TPTP parser does not appear to StopAtFirstErrorStrategy or StopAtFirstErrorSmtLibLexer but the SMT-LIB strategy does??

## operations 
Operations on terms are wrapped up in TermOps class.
Operations on theories are wrapped up in TheoryOps class.

To apply an operation to a term/theory using "wrap" as in 
operation.wrapTerm(t:term)
operation.wrapTheory(t:theory)

Operations are:
- DeBruijnConverter: converts a term to a term with DeBruijn var # (rather than names) @Joe where is this used
- InterpretationVerifier: verifies that an interpretation satisfies a theory.
- NormalForms: converts a theory/term to nnf; conversion to prenex normal form is not yet implemented.
- QuantifierExpander/QuantifierExpanderSimplifier:e xpands the quantifiers to And/Or using sort values; in the Simplifier one, the simplifier is called on each expansion.
- RecursiveAccumulator: functions that collect things like free variables, domain elements, constants, functions in a term. 
- RecursiveEliminators: replaces enumvalues/domain elements in terms with constants.
- RecursivePatterns: apply a function recursively over terms.
- Simplification: some simple simplifications (not true == false, two domain elements are not equal) @Joe - this is where Khadija's simplifications would be added I think.
- SimplificationWithRange: like the above, but range restrictions are passed as an argument and used to simplify formulas. @Joe - aren't range formulas mostly going to be disjunctions? how does this help with simplifications?
- Skolemization: skolemizes a term, which produces a new term, skolem constants and functions.
- SmtlibConversion: converts a term to the strings needed for SMT-LIB.
- Substitution: substitutes a term for a variable in a term.  Performs needed alpha-renaming to avoid variable capture. FastSubstitutor does a bunch of substitutions in parallel.
- TermConvertor: Converts Ints to Signed Bit Vector operations. @Joe - perhaps this file should be renamed to be more specific to ints?
- TermMetrics: various metrics on terms (depth of quantification, depth of nested functions, number of nodes in a term)
- TermVisitorWithTypeContext/TypeCheck/Context: typechecks a term.  Builds the context of quantified variables and their types.  All primitive term parts (constants, variables, function declarations are explicitly typed) sorted so there is no type inference here.


## compiler 
A packaging mechanism for a sequence of transformations.
Hierarchy:
- LogicCompiler: The "compile" method of a LogicCompiler takes a theory and scopes, and returns either CompilerError of CompilerResult (theory,decompileInterpretation,skipForNextInterpretation @Joe - what's this last one?)
    - TransformationCompiler: The "compile" method builds a problem state and applies transformers.
        - BaseFortressCompiler: Defines the transformer sequence usually applied, parameterized by symmetry breaking transformers.
            - FortressCompilers: Define the fortress compilers (Zero, ONE, etc) as the BaseFortressCompilers plus certain symmetry breaking.
@Joe - should ExperimentalCompilers be dropped?


## modelfind 
ModelFinder is the main fortress interface.  A model finder takes a solver as an argument. Takes a theory and performs solving on it returning a result (and an interpretation when appropriate).
Hierarchy:
- ModelFinder
    - CompilationModelFinder: A version of the ModelFinder with a compilation phase in it.
        - FortressModelFinders

Important methods:
1) setTheory(theory: Theory): Unit
2) setAnalysisScope(t: Sort, size: Int): Unit
3) setTimeout(milliseconds: Int): Unit
4) setBoundedIntegers(semantics: IntegerSemantics): Unit
5) checkSat(): ModelFinderResult
6) viewModel(): Interpretation
7) nextInterpretation(): ModelFinderResult
8) countValidModels(newTheory: Theory): Int
Integer semantics can be: UnboundedSemantics, ModularSignedSemantics(bitwidth: Int)
The default ModelFinder is FortressZero.

The main ModelFinders defined (which depend on certain Compilers chosen):
- FortressZERO - no symmetry breaking
- FortressONE - Claessen and Sorensson symmetry breaking only
- FortressTWO - functions first for symmetry breaking
- FortressTWO_SI - sort inference then functions first for symmetry breaking
- FortressTHREE - 
- FortressTHREE_SI

@Joe - why are the ModelFinderSettings separate from ModelFinder?


## logging 
EventLogging is the main trait with different classes for recording timing for various processes.


## interpretation 
This directory is data structures for representing the interpretation returned by a solver.
Hierarchy:
- Interpretation: the trait for interpretations.  Includes maps for sorts, constants, and functions.  An interpretation can be turned into a String, or turned into constraints.  Methods to do substitutions and filter.
    - BasicInterpretation: The most common class for the Interpretation trait.
    - EvaluationBasedInterpretation: @Joe - I'm lost on what the purpose of this file is.




## solverinterface 
@Joe 
    - SolverTemplate is mentioned in the README here but does not appear in the files.
    - SolverStrategy is here but does not seem to connect to anything
    - I wonder if there are too many layers of abstraction here?

These are ways of connecting to external solvers.  Fortress has a general SolverSession interface, but we found that using the term building interfaces of SMT solvers was very slow, so now fortress converts a theory to a string in SMT-LIB and this can be passed to any SMT-LIB solver.  We use Java'a ProcessBuilder class(?) to manage an interarctive session with the solver.  Currently we support Z3 and CVC4 and we map the returned instance back to fortress interpretations (ProcessSmtlibEvaluation).  Interaction with the incremental solver via the process builder has not been well tested. (@Joe?)
Class Hierarchy:
- SolverInterface: The main interface to the solvers implemented - creates sessions with particular solvers.
- SolverSession:Trait that creates an interactive session with an external solver. 
    - ProcessBuilderSolver: Trait extending SolverSession for solvers that interact with fortress via the Java process builder library. @Joe - has some SMT-specific stuff that might not belong here 
        - StandardProcessBuilderSolver: Extends ProcessBuilderSolver @Joe - this file is very SMT-LIB specific. 
            - ProcessSmtlibEvaluation: Maps the returned SmtLib instance to a Fortress Interpretation. (@Joe - odd name - ProcessSmtlibInterpretation or Instance?)
                - Z3CliSolver : An instance of StandardProcessBuilderSolver for Z3.
                - CVC4CliSolver:An instance of StandardProcessBuilderSolver for CVC4.
        - IncrementalProcessBuilderSolver: Extends ProcessBuilderSolver for interactions with an incremental solver
            - ProcessSmtlibEvaluation
                - Z3CliSolver: An instance of IncrementalProcessBuilderSolver for Z3.
- ProcessSession: Used by ProcessBuildSolver to manage the interactive session.

Main methods are:
1) setTheory - takes a theory (returns Unit)
2) addAxiom - takes an axiom and adds it to the theory (returns Unit)
3) solve - take a timeout value and returns a ModelFinderResult
4) solution - returns the interpretation from the solver



## sortinference 
Functions for performing sort inference to get least specific sorts.
@Joe - it would be good to add some explanation here.

## symmetry
@Joe - I'm going to need help understanding this code.

ExperimentalSymmetryBreakers: @Joe - seems to be mostly unused.


## transformers 
All the operations that transform a theory.  The theory is packaged as a ProblemState to remember information that is needed to undo transformations (such as skolemization). With respect to efficiency, each transformer may walk over the entire theory.  After quantifier expansion, theories can be quite large and in the future, we may wish to integrate some transformers for efficiency.

@Joe - README file doesn't mention problem state 
@Joe - some of these transformers have some preconditions - can we record in the ProblemState some information to ensure preconditions are met?  We should probably explain these in the order that they are typically used.

A ProblemState contains theory, scopes, skolemConstants, skolemFunctions, rangeRestrictions, unapplyInterp
Methods:
- apply - takes a theory and creates a ProblemState
        - takes a theory and scopes and creates a ProblemState

ProblemStateTransformer 
Methods:
- apply: takes a problem state and produces a problem state

TheoryTransformer
Methods:
- apply: takes a theory and produces a theory
- asProblemStateTransformer - turns a theoryTransformer into a problem state transformer

Hierarchy:
- ProblemStateTransformer
    - DomainEliminationTransformer2: like DomainEliminationTransformer but over ProblemState
    - DomainEliminationTransformer3: like DomainEliminationTransformer but over ProblemState
    - EnumEliminationTransformer: replace enum elements with constants; assert these constants are distinct
    - QuantifierExpansionTransformer: precondition: no enum sorts, skolemization done; @Joe - there seems to be an unused option to createWithDomElemsAsConstants; the comment says scopes must provide sizes for all sorts, but I don't think this is true any more - unbounded ints)
    - QuantifierExpansionSimplifier: @Joe - this one does not seem to be used?
    - RangeFormulaTransformer_NoElision: adds range formulas @Joe - explanasion is need wrt to the Elision or not
    - RangeFormulaTransformer: adds range formulas
    - SimplifyWithRangeTransformer: does simplify operations but includes range restrictions @Joe does this mean range formulas?  Also, the main compilers do not seem to use this (but rather use SimplifyTransformer below) which surprises me
    - SkolemizeTransformer: calls skolemize operation on each axiom; unapply removes the skolem constants/functions from the interpretations. @Joe - this has a precondition of being in NNF
    - SortInferenceTransformer: infers new sort; adds these sorts; unapply reverses the sort substitution
    - SymmetryBreakingTransformer_NoSkolem: adds symmetry breaking constraints to the theory
    - SymmetryBreakingTransformer
    - SymmetryBreakingTransformerSI
    @Joe - the differences between the three above need to be clarified; the NoSkolem one doesn't seem to be used, the SI one is used for SI Compilers
- TheoryTransformer
    - DomainEliminationTransformer: replace domain elements with constants; assert constants are distinct
    - IntegerFinitizationTransformer: replaces integers with bit vectors
    - NnfTransformer: turns axioms of theory into negation normal form using nnf operation
    - SimplifyTransformer: simplifies axioms of theory using using simplify operation
    - TypeCheckSanitize: do typchecking; make sure all axioms are of Bool sort. This is not done on-the-fly because it takes too much time to continually do it recursively throughout the term.  Throws an error or returns the same theory.

@Joe - why do we need three DomainEliminationTransformers? DomainEliminationTransformer2 seems to be the one used in the Fortress Compilers.
@Joe - would it be easier to just make everything ProblemStateTransformers (TheoryTransformers seem like a relic from when everything was TheoryTransformers)

## antlr 
FOFTPTP.g4 - parses TPTP
SmtLibSubset.g4 - parses SMT-LIB @joe is this SMT-LIB2?

