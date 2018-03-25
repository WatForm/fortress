# Fortress

This is a modified version of the Fortress library originally described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions" by Amirhossein Vakili and Nancy Day, [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf).

The original implementation is due to Amirhossein Vakili in 2016, with testing,
ocumentation, and hopefully some modification by Joseph Poremba in Winter 2018.

## Requirements
Gradle must be installed in order to build fortress. It is recommended you enable the Gradle Daemon to speed up building times.

Z3's command line interface must be installed in order to run fortress (for now at least, we plan to refactor to use the Z3 Java bindings in the future).  
It is highly recommended you use an up to date version of Z3 (4.6.0+), as memory bugs are known to appear in older versions ([a similar bug to this one appeared during one Fortress test](https://github.com/Z3Prover/z3/issues/631)).
Note that at time of writing, Z3 4.4.1 is the version that is installed when using `apt-get` on Ubuntu. It is recommended to use the precompiled binaries distributed instead ([available here](https://github.com/Z3Prover/z3/releases)).

## Building
#### Complete Build
Run `gradle build` to completely build fortress.
This includes:  
* Compilation
* Packaging zip and tar files for distribution
* Static analyzer (PMD)
* Unit Tests (JUnit)
* Coverage analyzer (Jacoco)
* Documentation (Javadoc)

#### Compilation
Run `gradle compileJava`.

#### Packaging
Run `gradle distZip` or `gradle distTar`.
This will create a zip or tar file respectively in the `build/distributions` directory.
`gradle assemble` will do both.
The archive will contain both the fortress jar and any runtime dependencies, such as ANTLR.

#### Static Analysis (PMD)
Run `gradle check`.
A report will be available in `build/reports/pmd/main.html` and `build/reports/findbugs/test.html`.

#### Unit Tests and Coverage
Run `gradle test`.
An HTML version of the test results will be avaiable at `build/reports/tests/index.html`.  
`gradle jacoco` will generate a coverage report in `build/reports/jacoco/test/html/index.html`.

Note: Gradle may not rerun tests that have already passed since the last change. To force it to rerun the tests, run `gradle cleanTest test`.

Note: There is another repository, fortress-tests, which runs tests on files (e.g. TPTP files).

#### Building Documentation
Run `gradle javadoc`.
The documentation can then be viewed in `build/docs/javadoc/index.html`.

## Plan for improvements
* Set up tests and restructure repository, which will also help to better understand fortress
* Documentation
* Add abstraction layers so changes can be made without breaking the interface
* Seperate out parser from core Fortress, maybe as a separate repository
* Decide the interface to publish for Fortress and whether the parser should be separate from the rest of Fortress, as it really just uses fortress as opposed to being part of the core
* Streamline the implementation by removing higher order logic layer
* Hunt for optimizations
* Switch from using Z3 on the commmand line to the Java API for Z3

## Implementation Notes
input -> `ANTLRInputStream` -> `FOFTPTPLexer` -> `CommonTokenStream`
-> `FOFTPTPParser` -> `ParseTree`

`FOF2Fortress` is a visitor for the parse tree.
It visits the nodes of the parse tree, which represent first order logic connectives (e.g. and, or, imp, pred).
At each node, it largely delegates to the `FOL` class (e.g. `FOL.mkForall`, `FOL.mkAnd`).

Rather than construct a first order logic formula directly, the `FOL` class constructs
each of these first order logic formulas by encoding it in the typed lambda calclus (the `Term` hierarchy).
`FOL` also contains static methods that accept a term and decide if it describes a
particular first order logic formula (e.g. `FOL.isNot`, `FOL.isEq`).

After visiting the parse tree and constructing the `Term`, `FOF2Fortress`
generates a new `Theory` object. This theory object uses the `Theory.ARITH_THEORY`
as a base, and adds the generated `Term` as an axiom.
(Question: it likely visits multiple formulas).


The `Formula` class has a static `fromTerm` method which takes a typed lambda calculus `Term`
and produces an explicit first order logic formula, uisng the `Formula` hierarchy.


