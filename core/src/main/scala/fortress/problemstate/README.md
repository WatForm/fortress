# README.md for ProblemState

A `ProblemState` holds:
- a theory
	+ theory may contain enums, which are constants of an exact/unchanging scope
- a mapping from sorts to scopes. A scope includes the attributes of being Exact/NonExact and Unchanging/Changing
	+ a Unchanging scope can never be NonExact (???)
	+ a scope can change from NonExact to Exact via transformers (but never the other way around)
	+ an Unchanging scope can NEVER be changed
	+ the user is allowed to change an Changing sort
	+ not every sort requires a scope (these are considered to have unbound scopes)
	+ intsort is included here if it has a scope
	+ **how are bit vectors handled**
 		- **OZ: Bitvectors use IntSort, choosing the minimal bitwidth to represent at least as many values as given in the scope of IntSort.**
  		- **NAD: arent's BitVectors a distinct sort from IntSort?**
   		- **OZ cont.: IntSort is then replaced with BitVectorSort(bitwidth). Notably, BitVectors keep their bitwidth in their Sort, and thus do not require a separate scope.**
   		- BV never appear in Scope map
	+ BoolSort should never be in this map
	+ **are there any other built-in sorts?**
		- **OZ: BoundedIntSort and UnboundedIntSort also exist. BoundedIntSort is converted to bitvectors, while UnboundedIntSort is skipped. UnboundedIntSort seems to be able to be added by the LiaCheckTransformer**
		- **take Unbounded/BoundedSort out**
	**NAD: I suspect it would be better to use the terminology Fixed/Nonfixed, as Changing does not mean much.**
- skolemConstants/skolemFunctions 
	+ these are added by the Skolemization transformer only
	+ they are used to understand interpretations
- rangeRestrictions
- unapplyInterp
- flags
	+ tell us the state of the problem - haveRunNNF, haveRunIfLifting, etc to provide some warnings if transformers are not run in the best sequence
- verbose
**NAD: it looks like the distinctConstants parameter mentioned in the comment in the problem state has disappeared**

### Execution sequences:
- create a problem state with a theory, calculate the exact/unchanging scope for sorts of enums
	- **should the user be required to put in scopes at this moment of creation?**
	- **should sorts be allowed to be added?**
		+ **OZ: I'm confused what this means. Can you elaborate? When? To the scopes map?**
		+ NAD: sorts exist in the theory and in the scope map, should scopes be allowed to be added to the scopemap after the theory is created?
	- **the EnumEliminationTransformer makes the sort of the enum ExactScope (so I'm not sure why we are doing something in ProblemState)**
- any NonExact scopes have to be removed before solving (**NAD: this should be a check somewhere in the Solver?**)
- changeable scopes could be removed (MaxUnboundScopesTransformer)
- changeable scopes could be changed (**I don't think we have any transformers that currently do this although I'm not sure where Hugsy' code went that iterated through increasing scopes**)
- changeable scopes could become unchangeable (iterative closures/eventually set cardinality)
- add skolem constants/functions (never removed)
- add to unapply (add to LIFO stack) (never removed)
- flags can be set (**never unset?**)
- not sure about how range restrictions are used **??**
- verbose should never be unset

### Additional Relevant Information

- the DEsAsDatatypeTransformer (used to be called DataTypeTransformer) seems to make DEs constants, how is this different than the ConstantsForDEsTransformers??  I have a feeling that these three are very similar and just differ in whether we add an axiom that the constants are distinct or not.  What actually choose whether datatypes are split out in SMT-LIB???

- right now ProblemState/Flags are case classes and we use .copy to change create a new copy of the ProblemState after each transformer  - this does allow the transformers pretty complete freedom
- if we made the ProblemState mutable then we could limit the methods of the ProblemState to only allow certain operations, e.g., changing something about the scope of the problemstate in a fixed way but never adding any sorts or changing Exact to NonExact, etc.
