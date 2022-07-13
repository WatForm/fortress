# Transformers  

This document describes the various transformers that have been implemented in Fortress and how to use them.

This document is under construction.

## Overall Strategies

There are currently a few overall strategies for using Fortress:

1. Constants Method

This is the method described in the original paper on Fortress where a finite set of distinct constants (called domain elements) are created to represent the 
values of elements in the sort, quantifier expansion is done over these domain elements and every function application/constant in the theory is 
constrained to return a value of the sort (these constraints are called range axioms).  This method results in a theory in EUF - a decidable subset of FOL.

2. Datatype Method

SMT solvers now provide datatypes declarations where the values of a sort can be declared.  In this method, datatype values are created for domain values.  
Range axioms and/or quantifier expansion can be done or not.  **Is this problem decidable?**

3. Minimal Method

In this method, only typechecking is done so that the SMT solver can work with the problem directly. The problem may not be decidable.

## Transformers

In this table, we should the transformers in order as they are used in the strategies above.  We show defaults and options for various groups.  
**Something about where transformers and compilers exist in the code**

req = required
def = default, could be replaced with nothing or options
opt = optional replacement for default



| Group | Transformer                                       | Constants (EUF)       | Datatype           | Minimal          |  Description             |
|:--------|:--------------------------------------------------|:---------------- |:-------------------|:-----------------|------------------------- |
| | TypecheckSanitizeTransformer                      |    req           | req               | req              | performs typechecking    |   
| | ScopeSubtypeTransformer                           |    req           | req               | req              | set up predicates for non-exact scopes |
| | EnumEliminationTransformer                        |    req           | req                | req              | Enums become ...         |
| Integers| IntegerToBitVectorTransformer                    |    def           | def                   |                  | Turn integers into BVs   |
| Transitive Closure | **something about closure transformers**| | | | |
| | SortInferenceTransformer                          | def      | def                 |                  | infer sorts for more symmetry breaking        |           
| | NnfTransformer                                    |    req           | def                 |                  |                          |
| | PnfTransformer                                    |    opt              |   opt                |                  | Not yet implemented        |
| | SkolemizeTransformer                              |    req           | def               |                  |         |
|Symmetry | SymmetryBreakingMonoOnlyAnyOrder| | | | |
|Symmetry | SymmetryBreakingFunctionsFirstAnyOrder| | | | |
|Symmetry | SymmetryBreakingMonoFirstThenFunctionsFirstAnyOrder| | | | |
|Symmetry | SymmetryBreakingLowArityFirstMostUsedFunctionFirstOrderFactory| | | | |
|Symmetry | something about SI here| | | | |
| | StandardQuantifierExpansionTransformer **seems to be some options**           |    req           | def                 |                  |         |
| | StandardRangeFormulaTransformer  **seems to be some options**                  |    req           | def                 |                  |         |
| Simplify | SimplifyTransformer                               |    def           | def                 |                  |         |
| Simplify| SplitConjunctionTransformer| | | | |
| Simplify| SimplifyLearnedLiteralsTransformer| | | | |
| Simplify| SimplifyTransfomer2| | | | |
| Simplify| SimplifyWithRangeTransformer| | | | |
| DomainElimination | DomainEliminationTransformer                      |    req           | -                 |                  |         |
| | DomainEliminationTransformer2|    req           | -                 |                  | non-exact scopes by non-distinct constants - to remove       |
| | DatatypeTransformer                               |                  | req            |                  |         |

**missing something about DefaultSymmetryBreakerFactoryDL(None)**

