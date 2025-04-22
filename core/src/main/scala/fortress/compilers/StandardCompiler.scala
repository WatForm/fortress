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
        CompilersRegistry.ListOfOne(ClosureEliminationSquareDefnsTransformer)

    def scopes: ListBuffer[ProblemStateTransformer] = 
        CompilersRegistry.ListOfOne(ScopeNonExactPredicatesTransformer)

    def integerHandler:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(IntOPFITransformer)

    def setCardinalityOrNot:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(NullTransformer)

    def ifLiftOrNot:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(IfLiftingTransformer)

    def skolemizeOrNot: ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(SkolemizeTransformer)

    // disjLimit of 3 seemed for perform the best on the Portus
    // benchmark suite
    def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
            disjLimit = Option(3)
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





