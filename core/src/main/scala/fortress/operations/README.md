# `fortress.operations` Package

The `fortress.operations` package contains operations on `Term`s, such as quantifier instantiation and type checking.


## Implementation Notes

The file RecursivePatterns contains abstractions that can be used to easily write an operation that walks over all terms but only changes some kinds of terms and just recurses through the rest.

Any visitors that have state or require intricate setup I attempted to avoid
you just being able to call their visit method.
Usually the visitor is inside a private nested class and there is some wrapper
class around it to prevent misuse.
