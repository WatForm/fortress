# Fortress

This is a modified version of the Fortress library originally described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions" by Amirhossein Vakili and Nancy Day, [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf).

The original implementation is due to Amirhossein Vakili in 2016, with testing,
ocumentation, and hopefully some modification by Joseph Poremba in Winter 2018.

## Requirements
* Gradle must be installed in order to build fortress
* Z3's command line interface must be installed in order to run fortress (for now at least, we plan to refactor to use the Z3 Java bindings in the future). I recommend you don't use version 4.4.1 or lower, due to memory bugs ([such as this](https://github.com/Z3Prover/z3/issues/631)) that have come up. As of now, 4.4.1 is the version that is installed when using `apt-get` on Ubuntu, so beware.

## Building
Run `gradle build`.

It is recommended you enable the Gradle Daemon to speed up subsequent builds.

## Running Unit Tests
Run `gradle test`. Running `gradle build` will also run the unit tests.

Gradle may not rerun tests that already passed since the last change. To force it to rerun the tests, run `gradle cleanTest test`.

Note: There is another repository, fortress-tests, which runs tests on files (e.g. TPTP files).

## Plan
1. Set up tests, which will also help to better understand fortress
2. Documentation
3. Add abstraction layers so changes can be made without breaking the interface
4. Streamline the implementation by removing higher order logic layer
5. Hunt for optimizations


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


