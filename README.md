# Fortress

This is a modified version of the Fortress library originally described in the paper "Finite Model Finding Using the Logic of Equality with Uninterpreted Functions" by Amirhossein Vakili and Nancy Day, [available here](https://cs.uwaterloo.ca/~nday/pdf/refereed/2016-VaDa-fm.pdf).

The original implementation is due to Amirhossein Vakili in 2016, with testing,
ocumentation, and hopefully some modification by Joseph Poremba in Winter 2018.

## Building
Run `gradle build`

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


