package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to 
import fortress.transformers.Definitions.EliminateUnusedTransformer
import fortress.symmetry._
import scala.collection.mutable.ListBuffer

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (skolemize, quant exp)
   include range formulas
*/
class DatatypeWithRangeEUFCompiler() extends StandardCompiler {

    override def enumerateFiniteValues: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.ListOfOne(DEsToEnumsTransformer)
    
}

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (nnf, skolemize, quant exp)
   don't use range formulas (b/c datatype limits output to finite)
*/
class DatatypeNoRangeEUFCompiler() extends DatatypeWithRangeEUFCompiler() {

    override def rangeFormulasOrNot: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.NullTransformerList
    
}


/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no skolemize/quantifier expansion)
   use range formulas 
*/
class DatatypeWithRangeNoEUFCompiler() extends DatatypeWithRangeEUFCompiler {
    override def quantifierHandler: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.NullTransformerList

    override def skolemizeOrNot: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.NullTransformerList

}

/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no nnf, no skolemization and no quantifier expansion)
   no range formulas (b/c datatype limits output to finite)
*/

class DatatypeNoRangeNoEUFCompiler() extends DatatypeWithRangeNoEUFCompiler {

    override def rangeFormulasOrNot: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.NullTransformerList

}

class DatatypeWithRangeEUFEvaluateCompiler extends DatatypeWithRangeEUFCompiler {
    override def simplifiers: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += EvaluateTransformer
        ts += SimplifyTransformer
        ts += EliminateUnusedTransformer
        ts
    }
}

class DatatypeNoRangeEUFEvaluateCompiler extends DatatypeNoRangeEUFCompiler {
    override def simplifiers: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += EvaluateTransformer
        ts += SimplifyTransformer
        ts += EliminateUnusedTransformer
        ts
    }
}
