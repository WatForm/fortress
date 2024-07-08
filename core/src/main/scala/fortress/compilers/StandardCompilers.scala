package fortress.compilers

//import fortress.msfol._
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
    def closureEliminator: ProblemStateTransformer = 
        ClosureEliminationEijckTransformer

    def nonExactScopeEliminator: ProblemStateTransformer = 
        ScopeNonExactPredicatesTransformer

    def integerHandler:ProblemStateTransformer = 
        OPFIIntsTransformer

    def ifLiftOrNot:ProblemStateTransformer =
        IfLiftingTransformer

    def skolemizeOrNot: ProblemStateTransformer =
        SkolemizeTransformer

    def symmetryBreaker:ProblemStateTransformer = 
        new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
        ))

    def quantifierHandler: Seq[ProblemStateTransformer] = { 
        val ts = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        ts += QuantifiersToDefinitionsTransformer
        ts += StandardQuantifierExpansionTransformer
        ts.toList
    }

    def rangeFormulasOrNot: ProblemStateTransformer = 
        RangeFormulaStandardTransformer

    def enumerateFiniteValues: ProblemStateTransformer = 
        DomainEliminationTransformer

    override def transformerSequence: Seq[ProblemStateTransformer] = {

        val transformerSequence = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        transformerSequence += TypecheckSanitizeTransformer
        transformerSequence += EnumEliminationTransformer

        // defined above
        transformerSequence += closureEliminator
        
        // defined above
        transformerSequence += nonExactScopeEliminator

        // defined above
        transformerSequence += integerHandler

        // defined above
        transformerSequence += ifLiftOrNot

        transformerSequence += NnfTransformer

        transformerSequence += MaxAlphaRenamingTransformer
        // eliminates the introduction of some skolem functions, but needs to come after nnf and max alpha renaming
        transformerSequence += SimplifyWithScalarQuantifiersTransformer
        transformerSequence += AntiPrenexTransformer

        // defined above
        transformerSequence += skolemizeOrNot

        // defined above
        transformerSequence += symmetryBreaker 

        // defined above
        transformerSequence ++= quantifierHandler

        // defined above
        transformerSequence += rangeFormulasOrNot

        transformerSequence += new SimplifyTransformer

        // defined above
        transformerSequence += enumerateFiniteValues

        transformerSequence.toList
    }



}

class ClaessenCompiler() extends StandardCompiler {

    override def closureEliminator: ProblemStateTransformer = 
        ClosureEliminationClaessenTransformer

}

class StandardSICompiler() extends StandardCompiler {

    override def symmetryBreaker:ProblemStateTransformer = 
        new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = true,
            patternOptimization = true,
        ))

}

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (skolemize, quant exp)
   include range formulas
*/
class DatatypeWithRangeEUFCompiler() extends StandardCompiler {

    override def enumerateFiniteValues: ProblemStateTransformer = 
        DatatypeTransformer
    
}

/*
   use datatypes but turn it into EUF by getting rid of quantifiers (nnf, skolemize, quant exp)
   don't use range formulas (b/c datatype limits output to finite)
*/
class DatatypeNoRangeEUFCompiler() extends DatatypeWithRangeEUFCompiler() {

    override def rangeFormulasOrNot: ProblemStateTransformer = 
        NullTransformer
    
}


/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no nnf, no skolemize/quantifier expansion)
   use range formulas 
*/
class DatatypeWithRangeNoEUFCompiler() extends StandardCompiler {
    override def quantifierHandler: Seq[ProblemStateTransformer] = {  
        // TODO: SHOULDN"T THIS BE NOTHING??
        val ts = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        ts += QuantifiersToDefinitionsTransformer
        ts.toList
    }

    override def ifLiftOrNot: ProblemStateTransformer =
        NullTransformer

    override def skolemizeOrNot: ProblemStateTransformer =
        NullTransformer

    override def enumerateFiniteValues: ProblemStateTransformer = 
        DatatypeTransformer
}

/*
   use datatypes 
   don't get rid of quantifiers - not EUF (no nnf, no skolemization and no quantifier expansion)
   no range formulas (b/c datatype limits output to finite)
*/

class DatatypeNoRangeNoEUFCompiler() extends DatatypeWithRangeNoEUFCompiler {

    override def quantifierHandler: Seq[ProblemStateTransformer] =  { 
        // TODO: SHOULDN"T THIS BE NOTHING??
        val ts = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        ts += QuantifiersToDefinitionsTransformer
        ts.toList
    }

    override def rangeFormulasOrNot: ProblemStateTransformer = 
        NullTransformer

    override def enumerateFiniteValues: ProblemStateTransformer = 
        DatatypeTransformer
}


