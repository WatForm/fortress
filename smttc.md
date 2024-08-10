# smttc File Format

Fortress reads (at the CLI or API) files in the smttc format. `.smttc` is a minor extension to the `.smt2` file format that includes a few special Fortress features.  These features are described below.

## Transitive Closure

smttc has a built-in operator for transitive closure.  Transitive closure expressions are written as `(closure R x y [fixedargs...])` or `(reflexive-closure R x y [fixedargs...])` for reflexive closure.

The term `(closure R start end)` evaluates to true if there is an edge from `start` to `end` in the transitive closure of `R`.
`R` should be the identifier for the relation to be closed over. `start` and `end` are terms.

Fortress also supports transitive closure over relations of higher airity.
Consider `R: A x A x B x C`. One can write `(closure R start end fixB fixC)` where `fixB` is a term of sort `B` and `fixC` is a term of sort `C`.
The closure then works as above over the relation `R'` where `(start, end) \in R'` if and only if `(start, end, fixB, fixC) \in R`.


## Scope Information

smttc supports three `set-info` keywords for setting scope information in the file:
- `:exact-scope` is used to set exact scopes
- `:nonexact-scope` is used to set non-exact scopes
- `:unchanging-scope` is used to specify which sorts Fortress is not allowed to change

Each of these keywords expects a string value. The `exact` and `nonexact` scope methods expect a series of optionally whitespace separated `(sort scope)` specifiers. Sort must be an identifier and scope must be an integer. There must be at least some amount of whitespace separating the sort and scope.

The specifier for unchanging scopes expects a series of `(sort)`s optionally separated by whitespace.

For example:
```smt2
(set-info :exact-scope "(A 1) (|Complicated Name!!| 3)")
(set-info :nonexact-scope "(B 2)")
(set-info :unchanging-scope "(A)(|Complicated Name!!|)")
```

## Domain Elements

Fortress understand constants declared using the prefix "\_@" to be domain elements in the input.  This means these are not declared as inputs and their uses are converted to an internal domain element term.  Note that this means one can't read an input smttc file and directly write the internal problem state resulting from parsing without transforming the internal problem state to remove domain elements.