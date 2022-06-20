package fortress.transformers

import fortress.util.Errors
import javax.xml.crypto.Data
import fortress.symmetry._

object Transformers {

    // NOTE: This could be improved by making it return something ??? => ProblemStateTransformer? Is this possible?
  
    def fromString(name: String): ProblemStateTransformer = name match {
        case "ClosureElimination" | "ClosureEliminationTransformer" => ClosureEliminationTransformer
        case "Datatype" | "DatatypeTransformer" => DatatypeTransformer
        case "DomainElimination" | "DomainEliminationTransformer" => DomainEliminationTransformer
        case "DomainElimination2" | "DomainEliminationTransformer2" => new DomainEliminationTransformer2()
        case "EnumElimination" | "EnumEliminationTransformer" => EnumEliminationTransformer
        case "IntegerFinitization" | "IntegerFinitizationTransformer" => Errors.API.doesNotExist("Use mkIntegerFinitizationTransformer")
        case "Nnf" | "NnfTransformer" => NnfTransformer
        case "QuantifierExpansion" | "QuantifierExpansionTransformer" => Errors.API.doesNotExist("Use mkQuantifierExpansionTransformer")
        case "RangeFormula" | "RangeFormulaTransformer" => Errors.API.doesNotExist("Use mkRangeFormulaTransformer")
        case "ScopeSubtype" | "ScopeSubtypeTransformer" => new ScopeSubtypeTransformer()
        case "SimplifyLearnedLiterals" | "SimplifyLearnedLiteralsTransformer" => new SimplifyLearnedLiteralsTransformer()
        case "Simplify" | "SimplifyTransformer" => new SimplifyTransformer()
        case "Simplify2" | "SimplifyTransformer2" => new SimplifyTransformer2()
        case "SimplifyWithRange" | "SimplifyWithRangeTransformer" => new SimplifyWithRangeTransformer()
        case "Skolemize" | "SkolemizeTransformer" => SkolemizeTransformer
        case "SortInference" | "SortInferenceTransformer" => SortInferenceTransformer
        case "SplitConjunction" | "SplitConjunctionTransformer" => SplitConjunctionTransformer
        case "SymmetryBreaking_MostUsed" | "SymmetryBreakingTransformer_MostUsed" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_MostUsed")
        case "SymmetryBreaking_NoSkolem" | "SymmetryBreakingTransformer_NoSkolem" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer_NoSkolem")
        case "SymmetryBreaking" | "SymmetryBreakingTransformer" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformer")
        case "SymmetryBreakingSI" | "SymmetryBreakingTransformerSI" => Errors.API.doesNotExist("Use mkSymmetryBreakingTransformerSI")
        case "TypecheckSanitizer" | "TypecheckSanitizerTransformer" => TypecheckSanitizeTransformer
        case _ => Errors.API.doesNotExist(name + " is not a recognized Transformer.")
    }

    def mkClosureEliminationTransformer() = ClosureEliminationTransformer
    def mkDatatypeTransformer() = DatatypeTransformer
    def mkDomainEliminationTransformer() = DomainEliminationTransformer
    def mkDomainEliminationTransformer2() = new DomainEliminationTransformer2()
    def mkEnumEliminationTransformer() = EnumEliminationTransformer
    def mkIntegerFinitizationTransformer(bitwidth: Int): IntegerFinitizationTransformer = new IntegerFinitizationTransformer(bitwidth)
    def mkNnfTransformer() = NnfTransformer
    def mkQuantifierExpansionTRansformer(useConstForDomElim: Boolean, useSimplification: Boolean) = new QuantifierExpansionTransformer(useConstForDomElim, useSimplification)
    def mkRangeFormulaTransformer(useConstForDomElim: Boolean) = new RangeFormulaTransformer(useConstForDomElim)
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
