# Fortress Technical Guide

## Overview

## Idealized Fortress Pipeline
The "idealized" algorithm which Fortress implements is given by the following steps.

1. Negation Normal Form (NNF)
2. Skolemization
3. Symmetry Breaking
4. Universal Expansion
5. Simplification
6. Range Formulas
7. Domain Elimination
8. Scope Removal and SMT Invocation

A note on some technical definitions.

Two problems are "equivalent" when every interpretation satisfies one if and only if it satisfies the other.
In order for two problems to be equivalent, they must have the same signature (otherwise it doesn't make sense to evaluate them using the same interpretation).

Two problems are "equisatisfiable" when the answer to the question of their satisfiability is the same: that is, either both are SAT or both are UNSAT.
Equivalent problems are always equisatisfiable, but equisatisfiable problems need not be equivalent.
Equisatisfiable problems do not need to have the same signature; the only thing that matters is the answer to their satisfiability questions is the same.

The "unbounded" version of problem is the problem obtained by removing the scopes on any bound sorts.

A problem is "formulaically bound" if the following two conditions hold: the only interpretations that satisfy the unbounded version of the problem are those that satisfy the original (bounded) version.
If a problem is formulaically bound, it is equisatisfiable with its unbounded version.

All that Fortress needs to guarantee is that after its transformations, the final problem is equisatisfiable to the first input problem.

### Explanation of Steps

#### 1. Negation Normal Form
The formulas of the problem are transformed into negation normal form, where negations are pushed down as far as possible into the formulas.
The resulting problem is equivalent to the first.

#### 2. Skolemization
Existential quantifiers are eliminated by replacing them with functions and constants.
The signature is changed by the introduction of new functions and constants.
This operation must be performed after putting formulas into negation normal form, as otherwise it is impossible to tell which quantifiers are truly existential (since negations flip quantifiers).
Given this condition however, the resulting problem is equisatisfiable to the input problem.

#### 3. Symmetry Breaking
Additional constraints are added to reduce the number of interpretations that need to be checked by the solver.
The resulting problem is equisatisfiable to the input to this step.

#### 4. Universal Expansion
Universal quantifiers of bounded sorts are expanded by taking each possible instantiation and then taking their conjunction.
The resulting problem is equivalent to the input to this step.

#### 5. Simplification
The formulas are simplified as much as possible.
The resulting problem is equivalent to the input to this step.

#### 6. Range Formulas
Range formulas are introduced, which use the scopes to explicitly list the possible output values of each function and constant.
These range formulas are quantifier-free, so as to not introduce any more quantifiers after universal expansion.
The resulting problem is both equisatisfiable to the input to this step and *formulaically bound*.

#### 7. Domain Elimination
Constants are introduced to "simulate" the domain elements.
Specifically, for each domain element in the problem, a unique constant is generated.
It is asserted that these constants are mutually distinct from each other.
The domain elements are then replaced with their respective constants.
The resulting problem is equisatisfiable to the input to this step, and contains no domain elements.
This operation also maintains the property of being formulaically bound.

#### 8. Scope Removal and SMT Invocation
The unbounded version of this final problem is converted into a format that is accepted by an SMT solver (the problem contains no domain elements, so this can be done).
The SMT solver is then invoked.
Whatever result the solver returns is then returned to the user.

### Correctness
After applying the 7 transformations, the final problem is:
* equisatisfiable to the original problem, and
* formulaically bound (so its scopes can be removed).

Therefore, removing the scopes still leaves a problem equisatisfiable to the original, and, provided the SMT solver gives a correct result, so too does Fortress.

### Decision Procedure
If the original problem gives a scope for every sort, then because of the universal expansion step, there are no quantifiers in the final unbounded problem sent to the SMT solver.
Such problems fall under the fragment of first-order logic called the logic of equality with uninterpreted functions (EUF), which is decidable.
In SMT literature, this logic is called the logic of quantifier-free uninterpreted functions (QF_UF).
SMT solvers are decision procedures for such problems, and therefore so too is Fortress.


## Pipeline Optimizations
