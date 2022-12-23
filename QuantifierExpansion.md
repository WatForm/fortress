# Quantifier Expansion Ideas

Quantifier expansion is a bottleneck for Fortress - it creates large terms that can lead to memory overflow before the problem even reaches the SMT solver.  

We don't know if the SMT solver can handle large terms better than Fortress can.  Below are some possible solutions for QUF problems:

The memory overflow is occurring internally within the creation of terms in Fortress in the quantifier expansion step.

1. Use Datatypes in the SMT solver

If all sorts are limited in their set of values then the problem is decidable, but we don't know if the solver's algorithms recognize this as a decidable problem.

(1A) assume the use of datatypes makes the solver think the problem is finite and exists/forall quantifiers are okay (already added to FortressCompilers.scala) ClosureElimination requires nnf so we can't get rid of that step. For testing with QUF we might want to simplify this further.

```
abstract class DatatypeMethodNoRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }
}
```


(1B) datatypes plus range formulas (already added to FortressCompilers.scala)

```
abstract class DatatypeMethodWithRangeCompiler() extends LogicCompiler {
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer
        transformerSequence += ClosureEliminationEijckTransformer
        transformerSequence += IntegerToBitVectorTransformer      
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypeTransformer
        transformerSequence.toList
    }
}
```    
(1C) not much point in trying datatypes plus quantifier expansion because that makes the terms just as big

2. Use Definitions to avoid some of the expansion

(2A) Use Definitions with constants method

* requires creation of StandardQuantifierExpansionWithDefintionsTransformer that creates a defn for every quantifier expansion; have to watch that bound variables become arguments to nested quantifier expansions
``` 
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += NnfTransformer  
        transformerSequence += SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += StandardQuantifierExpansionWithDefinitionsTransformer // new 
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DomainEliminationTransformer
        transformerSequence.toList
    }
```

(2B) Use Definitions with datatypes method (1B but with quantifier expansion)

```
    override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer
        transformerSequence += new SymmetryBreakingTransformer(MonoFirstThenFunctionsFirstAnyOrder, DefaultSymmetryBreaker)
        transformerSequence += StandardQuantifierExpansionWithDefintionsTransformer
        transformerSequence += RangeFormulaStandardTransformer
        transformerSequence += new SimplifyTransformer
        transformerSequence += DatatypesTransformer
        transformerSequence.toList
    }
```

3. Use definitions for quantifier expansion but axiomatize the definitions, which would bring more quantifier expansion so doesn't seem like a good idea.  There does not seem to be a method that let's quantifier expansion be "abstracted" into a package that the solver can take advantage of.

4. If the problem is only within Fortress, i.e., the SMT solver can handle the large terms b/c it does some kind of term sharing underneath then we could try for a more optimized method of representing the terms within Fortress (i.e., term sharing). Perhaps we can integrate the quantifier expansion with the use of the Z3 API for term creation?

5. Integration the quantifier expansion with simplification?

---

Ideas for reducing quantifier cost from the Portus end:

1. Implement the idea to put sigs in separate sorts when possible to avoid making the univ scope so large, so quantifying over it isn't so expensive.
2. Implement (some) scope restrictions with cardinality (like `#A <= 10`) rather than nested quantifiers (like `exists x1,x2,...,x10: univ . forall y: univ . x1 in A && ... && x10 in A && (disj x1,...,xn) && y in A => y = x1 || ... || y = x10`). This seems to be a major cause of OOMs when doing quantifier expansion: growing scopes too large even in simple models seems to result in OOMs. The implementation of cardinality uses a single (expanded) quantifier so this could be more optimal.
