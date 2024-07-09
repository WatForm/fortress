# `fortress.transformers` Package

The `fortress.transformers` package contains the `TheoryTransformer` trait (interface), which is a representation of a function that takes in a `Theory` as input and produces a `Theory`.
The package contains many concrete implementations of `TheoryTransformer`, for purposes such as instantiating quantifiers or putting formulas in negation normal form.


Every transformer (at the API/CLI level) must be an object that takes no parameters (so that a string can match a class name).