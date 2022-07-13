package fortress.transformers

import fortress.util.Errors
import javax.xml.crypto.Data
import fortress.symmetry._

object Transformers {

    // NOTE: This could be improved by making it return something ??? => ProblemStateTransformer? Is this possible?
  
    def fromString(name: String): ProblemStateTransformer = name.toLowerCase() match {
        case "closureelimination" | "closureeliminationtransformer" => ClosureEliminationTransformer
        case "datatype" | "datatypetransformer" => DatatypeTransformer
        case "domainelimination" | "domaineliminationtransformer" => DomainEliminationTransformer
        case "domainelimination2" | "domaineliminationtransformer2" => new DomainEliminationTransformer2()
        case "enumelimination" | "enumeliminationtransformer" => EnumEliminationTransformer
        case "integerfinitization" | "integerfinitizationtransformer" => Errors.API.doesNotExist("Use mkIntegerFinitizationTransformer")
        case "nnf" | "nnftransformer" => NnfTransformer
        case "quantifierexpansion" | "quantifierexpansiontransformer" => mkQuantifierExpansionTRansformer()
        case "rangeformula" | "rangeformulatransformer" => mkRangeFormulaTransformer()
        case "scopesubtype" | "scopesubtypetransformer" => new ScopeSubtypeTransformer()
        case "simplifylearnedliterals" | "simplifylearnedliteralstransformer" => new SimplifyLearnedLiteralsTransformer()
        case "simplify" | "simplifytransformer" => new SimplifyTransformer()
        case "simplify2" | "simplifytransformer2" => new SimplifyTransformer2()
        case "simplifywithrange" | "simplifywithrangetransformer" => new SimplifyWithRangeTransformer()
        case "skolemize" | "skolemizetransformer" => SkolemizeTransformer
        case "sortinference" | "sortinferencetransformer" => SortInferenceTransformer
        case "splitconjunction" | "splitconjunctiontransformer" => SplitConjunctionTransformer
        case "symmetrybreaking_mostused" | "symmetrybreakingtransformer_mostused" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_MostUsed")
        case "symmetrybreaking_noskolem" | "symmetrybreakingtransformer_noskolem" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_NoSkolem")
        case "symmetrybreaking" | "symmetrybreakingtransformer" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer")
        case "symmetrybreakingsi" | "symmetrybreakingtransformersi" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformerSI")
        case "typechecksanitizer" | "typechecksanitizertransformer" => TypecheckSanitizeTransformer
        case _ => Errors.API.doesNotExist(name + " is not a recognized Transformer.")
    }

    def mkClosureEliminationTransformer() = ClosureEliminationTransformer
    def mkDatatypeTransformer() = DatatypeTransformer
    def mkDomainEliminationTransformer() = DomainEliminationTransformer
    def mkDomainEliminationTransformer2() = new DomainEliminationTransformer2()
    def mkEnumEliminationTransformer() = EnumEliminationTransformer
    def mkIntegerFinitizationTransformer(bitwidth: Int): IntegerFinitizationTransformer = new IntegerFinitizationTransformer(bitwidth)
    def mkNnfTransformer() = NnfTransformer
    def mkQuantifierExpansionTRansformer(useConstForDomElim: Boolean = false, useSimplification: Boolean = false) = new QuantifierExpansionTransformer(useConstForDomElim, useSimplification)
    def mkRangeFormulaTransformer(useConstForDomElim: Boolean = false) = new RangeFormulaTransformer(useConstForDomElim)
    def mkScopeSubtypeTransformer() = new ScopeSubtypeTransformer()
    def mkSimplifyLearnedLiteralsTransformer() = new SimplifyLearnedLiteralsTransformer()
    def mkSimplifyTransformer() = new SimplifyTransformer()
    def mkSimplifyTransformer2() = new SimplifyTransformer2()
    def mkSimplifyWithRangeTransformer() = new SimplifyWithRangeTransformer()
    def mkSkolemizeTransformer() = SkolemizeTransformer
    def mkSortInferenceTransformer() = SortInferenceTransformer
    def mkSplitConjunctionTransformer() = SplitConjunctionTransformer
    def mkSymmetryBreakingTransformer_MostUsed(selectionHeuristicWithConstantsFactory: SelectionHeuristicWithConstantsFactory, symmetryBreakerFactoryDL: SymmetryBreakerFactoryDL) = {
        new SymmetryBreakingTransformer_MostUsed(selectionHeuristicWithConstantsFactory, symmetryBreakerFactoryDL)
    }
    def mkSymmetryBreakingTransformer_NoSkolem(selectionHeuristic: SelectionHeuristic, symmetryBreakerFactory: SymmetryBreakerFactory) = new SymmetryBreakingTransformer_NoSkolem(selectionHeuristic, symmetryBreakerFactory)
    def mkSymmetryBreakingTransformer(selectionHeuristic: SelectionHeuristic, symmetryBreakerFactory: SymmetryBreakerFactory) = new SymmetryBreakingTransformer(selectionHeuristic, symmetryBreakerFactory)
    def mkSymmetryBreakingTransformerSI(selectionHeuristic: SelectionHeuristic, symmetryBreakerFactory: SymmetryBreakerFactory) = new SymmetryBreakingTransformerSI(selectionHeuristic, symmetryBreakerFactory)
    def mkTypecheckSanitizeTransformer() = TypecheckSanitizeTransformer
}
