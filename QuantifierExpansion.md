# Quantifier Expansion Ideas

Quantifier expansion is a bottleneck for Fortress - it creates large terms that can lead to memory overflow before the problem even reaches the SMT solver.  

We don't know if the SMT solver can handle large terms better than Fortress can.  Below are some possible solutions for QUF problems:

1. Is the memory overflow occurring internally within the creation of terms in Fortress (i.e., in the quantifier expansion step) or in the process of creating the SMT term to send to the solver) ?  If it is in the process of creating the SMT term then using the Z3 API might help.

2. Use Datatypes in the SMT solver

If all sorts are limited in their set of values then the problem is decidable, but we don't know if the solver's algorithms recognize this as a decidable problem.

(2A) assume the use of datatypes makes the solver think the problem is finite and exists/forall quantifiers are okay

'''
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
'''


(2B) datatypes plus range formulas

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
    
(2C) not much point in trying datatypes plus quantifier expansion because that makes the terms just as big

3. Use Definitions to avoid some of the expansion

(3A) Use Definitions with constants method

* requires creation of StandardQuantifierExpansionWithDefintionsTransformer that creates a defn for every quantifier expansion; have to watch that bound variables become arguments to nested quantifier expansions
 
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

(3B) Use Definitions with datatypes method (2B but with quantifier expansion)

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
    
4. Use definitions for quantifier expansion but axiomatize the definitions, which would bring more quantifier expansion so doesn't seem like a good idea.  There does not seem to be a method that let's quantifier expansion be "abstracted" into a package that the solver can take advantage of.

5. If the problem is only within Fortress, i.e., the SMT solver can handle the large terms b/c it does some kind of term sharing underneath then we could try for a more optimized method of representing the terms within Fortress (i.e., term sharing). Perhaps we can integrate the quantifier expansion with the use of the Z3 API for term creation?

6. Integration the quantifier expansion with simplification? 
