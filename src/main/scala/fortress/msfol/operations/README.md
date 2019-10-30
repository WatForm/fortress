# `fortress.msfol.operations` Package

The `fortress.msfol.operations` package contains operations on `Term`s, such as quantifier instantiation and type checking.

## Implementation Notes

Any visitors that have state or require intricate setup I attempted to avoid
you just being able to call their visit method.
Usually the visitor is inside a private nested class and there is some wrapper
class around it to prevent misuse.
