package fortress.transformers

// every transformer has to be registered here

import fortress.util.Errors
import javax.xml.crypto.Data
import fortress.symmetry._

object Transformers {

    // NOTE: This could be improved by making it return something ??? => ProblemStateTransformer? Is this possible?
  
    def fromString(name: String): ProblemStateTransformer = {
        var transformerName = name.toLowerCase()
        // Remove "transformer tail"
        // While this doesn't perfrectly match XTransformer2, we want to rename these anyway
        if (transformerName.endsWith("transformer")) {
            transformerName = transformerName.substring(transformerName.length() - 11)
        }
        transformerName match {
            case "closureeliminationeijck" => ClosureEliminationEijckTransformer
            case "closureeliminationliu" => ClosureEliminationLiuTransformer
            case "closureeliminationsquare" => ClosureEliminationSquareTransformer
            case "closureeliminationclaessen" => ClosureEliminationClaessenTransformer
            case "closureeliminationiterative" => ClosureEliminationIterativeTransformer
            case "datatype" => DatatypeTransformer
            case "domainelimination" => DomainEliminationTransformer
            case "domainelimination2" | "domaineliminationtransformer2" => new DomainEliminationTransformer2()
            case "enumelimination" => EnumEliminationTransformer
            case "integertobitvectors" => IntegerToBitVectorTransformer
            case "nnf" => NnfTransformer
            case "quantifierexpansion" => mkQuantifierExpansionTransformer()
            case "rangeformula" | "rangeformulastandard" => RangeFormulaStandardTransformer
            case "scopenonexactpredicatestype" => new ScopeNonExactPredicatesTransformer()
            case "simplifylearnedliterals" => new SimplifyLearnedLiteralsTransformer()
            case "simplify" => new SimplifyTransformer()
            case "simplify2" | "simplifytransformer2" => new SimplifyTransformer2()
            case "simplifywithrange" => new SimplifyWithRangeTransformer()
            case "skolemize" => SkolemizeTransformer
            case "sortinference" => SortInferenceTransformer
            case "splitconjunction" => SplitConjunctionTransformer
            case "symmetrybreaking_mostused" | "symmetrybreakingtransformer_mostused" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_MostUsed")
            case "symmetrybreaking_noskolem" | "symmetrybreakingtransformer_noskolem" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_NoSkolem")
            case "symmetrybreaking" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer")
            case "symmetrybreakingsi" | "symmetrybreakingtransformersi" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformerSI")
            case "typechecksanitizer" => TypecheckSanitizeTransformer
            case _ => Errors.API.doesNotExist(name + " is not a recognized Transformer.")
        }
    }

    // def mkClosureEliminationTransformer() = ClosureEliminationTransformer
    def mkDatatypeTransformer() = DatatypeTransformer
    def mkDomainEliminationTransformer() = DomainEliminationTransformer
    def mkDomainEliminationTransformer2() = new DomainEliminationTransformer2()
    def mkEnumEliminationTransformer() = EnumEliminationTransformer
    def mkNnfTransformer() = NnfTransformer
    def mkQuantifierExpansionTransformer(useConstForDomElim: Boolean = false, useSimplification: Boolean = false) = new QuantifierExpansionTransformer(useConstForDomElim, useSimplification)
    // def mkRangeFormulaTransformer(useConstForDomElim: Boolean = false) = new RangeFormulaStandardTransformer
    def mkScopeNonExactPredicatesTransformer() = new ScopeNonExactPredicatesTransformer()
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
