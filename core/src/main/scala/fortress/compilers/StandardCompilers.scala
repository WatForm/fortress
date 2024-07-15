package fortress.compilers

//import fortress.msfol._
import fortress.operations._
import fortress.transformers.Definitions.EliminateUnusedTransformer
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


// the default values here are for the constants method
    // using constants for DEs
    // have to get rid of quantifiers (skolemize, quant exp)
    // need range formulas
// which turns the theory into EUF (except for whatever is done for integers)

class StandardCompiler extends BaseCompiler {

    // these top definitions are the most common variation points
    def closureEliminator: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(ClosureEliminationEijckTransformer)

    def scopes: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(ScopeNonExactPredicatesTransformer)

    def integerHandler:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(IntOPFITransformer)

    def setCardinalityOrNot:ListBuffer[ProblemStateTransformer] =
        ListOfOne(NullTransformer)

    def ifLiftOrNot:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(IfLiftingTransformer)

    def skolemizeOrNot: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(SkolemizeTransformer)

    def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
        )))

    def quantifierHandler: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += QuantifiersToDefnsTransformer
        ts += QuantifierExpansionTransformer
        ts
    }

    def rangeFormulasOrNot: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(RangeFormulaUseDEsTransformer)

    def simplifiers: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += EvaluateTransformer
        ts += SimplifyTransformer
        ts += EliminateUnusedTransformer
        ts 
    }

    def enumerateFiniteValues: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.ListOfOne(DEsToDistinctConstantsTransformer)

    override def transformerSequence: Seq[ProblemStateTransformer] = {

        val transformerSequence = CompilersRegistry.NullTransformerList
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumsToDEsTransformer

        // defined above
        transformerSequence ++= closureEliminator

        // defined above
        transformerSequence ++= scopes

        // defined above
        transformerSequence ++= integerHandler

        // defined above (set to null as default)
        transformerSequence ++= setCardinalityOrNot

        // defined above
        transformerSequence ++= ifLiftOrNot

        transformerSequence += NnfTransformer

        transformerSequence += MaxAlphaRenamingTransformer
        // eliminates the introduction of some skolem functions, but needs to come after nnf and max alpha renaming
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += AntiPrenexTransformer

        // defined above
        transformerSequence ++= skolemizeOrNot

        // defined above
        transformerSequence ++= symmetryBreaker

        // defined above
        transformerSequence ++= quantifierHandler

        // defined above
        transformerSequence ++= rangeFormulasOrNot

        transformerSequence ++= simplifiers

        // defined above
        // must be done to eliminate all DEs
        // conversion to constants or datatypes(enums)
        // is necessary before can write SMT-LIB output
        // for either solving or compileOnly
        transformerSequence ++= enumerateFiniteValues

        transformerSequence.toList
    }



}

class EijckCompiler() extends StandardCompiler {

    override def closureEliminator: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(ClosureEliminationEijckTransformer)

}


class StandardSICompiler() extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(
            new SymmetryBreakingTransformer(SymmetryBreakingOptions(
                selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
                breakSkolem = true,
                sortInference = true,
                patternOptimization = true,
            )))

}

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
   don't get rid of quantifiers - not EUF (no nnf, no skolemize/quantifier expansion)
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

class MaxUnboundedScopesCompiler extends StandardCompiler {
    override def scopes: ListBuffer[ProblemStateTransformer] = {
        val ts:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.NullTransformerList
        ts += MaxUnboundedScopesTransformer
        ts += ScopeNonExactPredicatesTransformer
        ts
    }
}

class EvaluateCompiler extends StandardCompiler {
    override def quantifierHandler: ListBuffer[ProblemStateTransformer] = 
        // no QuantifiersToDefnsTransformer
        CompilersRegistry.ListOfOne(QuantifierExpansionTransformer)

    override def simplifiers: ListBuffer[ProblemStateTransformer] = {
        val ts = CompilersRegistry.NullTransformerList
        ts += EvaluateTransformer
        ts += SimplifyTransformer
        ts += EliminateUnusedTransformer
        ts
    }
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
