# Quantifier simplification operations in Fortress

There are several new optimizations in Fortress which manipulate and eliminate quantifiers.
They are implemented mostly in `fortress.operations.NormalForms`.
Many of the ideas here are from "Minimizing Disjunctive Normal Forms of Pure First-Order Logic" by Timm Lampert,
Logic Journal of the IGPL 25.3 2017 <https://www2.cms.hu-berlin.de/newlogic/webMathematica/Logic/minimizingDNFFOL.pdf>.

## Miniscoping

*Miniscoping* attempts to push quantifiers inwards into a formula as far as possible without reordering them.
Miniscoping is defined in Lampert. The following transformations are applied as much as possible:
```
forall x . P & Q     -->  (forall x . P) & (forall x . Q)
exists x . P | Q     -->  (exists x . P) | (exists x . Q)
forall x . P(x) | Q  -->  (forall x . P(x)) | Q  where Q does not mention x
exists x . P(x) & Q  -->  (exists x . P(x)) & Q  where Q does not mention x
```
Note that the last two rewriting rules are only valid because Fortress sorts cannot be empty (that is, if the sort of
`x` were empty, the rule would be unsound).
These rules are applied repeatedly until fixpoint (although our implementation takes only one pass).
We also eliminate useless quantifiers where the body does not mention the quantified variable such as `forall x . P`
where `P` does not mention `x`.

The aim of miniscoping is to reduce the scope of each quantifier so that when quantifier expansion is run, the expanded
formula is as small as possible. However, miniscoping on its own does not reduce the scopes optimally since it does not
reorder quantifiers. For example, the following formula adapted from Lampert is miniscoped according to the above:
```
exists y . exists x . q(y,x) & r(x)
```
It is however equivalent to the following formula in which the inner quantifier has a smaller scope:
```
exists x . (exists y . q(y,x)) & r(x)
```

Miniscoping is implemented in `fortress.operations.NormalForms.miniscope`.

## Partial prenexing

*Partial prenexing* brings existential quantifiers upwards through conjunctions and universal quantifiers upwards
through disjunctions. The aim is to allow all relevant conjuncts/disjuncts to be viewed at once for each set of
consecutive quantifiers of the same type. One application of this is to allow quantifier sorting for optimizations such
as in the previous example.

As defined in Lampert, the following transformations are applied as much as possible:
```
(forall x . P) | Q  -->  forall x . P | Q
(exists x . P) & Q  -->  exists x . P & Q
```
Partial prenexing is implemented in `fortress.operations.NormalForms.partialPrenex`.

## Anti-prenex normal form

*Anti-prenexing*, as defined in Lampert and implemented in `fortress.operations.NormalForms.antiPrenex`, is performed
as follows:

1. Miniscope.
2. Partial prenex in order to view all runs of consecutive quantifiers of the same type at once.
3. Sort runs of consecutive quantifiers of the same type as described below.
4. Miniscope again to minimize scopes.

In step 3, consecutive quantifiers of the same type are sorted in the reverse order of the number of conjuncts (for
existential quantifiers) or disjuncts (for universal quantifiers) in the body that mention the variable bound by the
quantifier. That is, quantifiers whose bound variable is mentioned among fewer conjuncts/disjuncts are sorted later in
the list of quantifiers. Lampert called this "prenex sorting". For example, in the example from earlier:
```
exists y . exists x . q(y,x) & r(x)
```
Since `x` appears in both conjuncts but `y` only appears in one conjunct, `y` is sorted after `x`:
```
exists x . exists y . q(y,x) & r(x)
```
The second round of miniscoping in step 4 then produces the minimal-scope formula:
```
exists x . (exists y . q(y,x)) & r(x)
```

Anti-prenexing prepares the formula for quantifier expansion by minimizing the scope and is implemented in
`AntiPrenexTransformer`.

## Scalar quantifier simplifier

The goal of the scalar quantifier simplifier (`SimplifyWithScalarQuantifiersTransformer`) is to eliminate quantifiers
in the following schemes, where `c` is a constant (or externally bound variable):
```
exists x . x = c & P(x)     -->  P(c)
forall x . !(x = c) | P(x)  -->  P(c)
```
However, before applying this simplification, we sometimes need to push in or pull up quantifiers to be able to see all
relevant equality terms:
```
(1) exists x . (x = a & P(x)) | (x = b & P(x))
  should be transformed to
    (exists x . x = a & P(x)) | (exists x . x = b & P(x))
  and then simplified to
    P(a) | P(b)

(2) exists x . P(x) & (exists y . x = f(y) & Q(y))
  should be transformed to
    exists x, y . P(x) & x = f(y) & Q(y)
  and then simplified to
    exists y . P(f(y)) & Q(y)
```

To handle a wide variety of cases, we do the following:

1. Anti-prenex to handle cases such as (1).
2. Partial prenex to see all relevant equality terms, handling cases such as (2).
3. Run *simplification with scalar quantifiers*, which eliminates quantifiers using equalities as shown above.

The above is implemented in `SimplifyWithScalarQuantifiersTransformer`. Compilers should then run
`AntiPrenexTransformer` to put the formula back in anti-prenex normal form in preparation for quantifier expansion.