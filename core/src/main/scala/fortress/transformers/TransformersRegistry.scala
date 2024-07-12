package fortress.transformers

import fortress.util.Errors
import javax.xml.crypto.Data
import fortress.symmetry._

// look up transformer associated with a string name
// raise an exception if not found
object TransformersRegistry {



    def fromString(name: String): ProblemStateTransformer = {

        // the comments here match the directory names and the variation points in the StandardCompiler
        val t:ProblemStateTransformer = name match {

            // string name must match the object name + 'Transformer'
            case "EnumsToDEsElimination" => EnumsToDEsTransformer
            case "IfLifting" => IfLiftingTransformer
            case "Nnf" => NnfTransformer
            case "Null" => NullTransformer
            case "QuantifierExpansion" => QuantifierExpansionTransformer
            case "RangeFormulaUseDEs" => RangeFormulaUseDEsTransformer
            case "RangeFormulaUseConstants" => RangeFormulaUseConstantsTransformer
            case "SortInference" => SortInferenceTransformer
            // options can be set in symmetry breaking to vary its behaviour
            case "SymmetryBreakingWithDefaults" => SymmetryBreakingWithDefaultsTransformer
            case "TypecheckSanitize" => TypecheckSanitizeTransformer

            // ClosureEliminator
            case "ClosureEliminationEijck" => ClosureEliminationEijckTransformer
            case "ClosureEliminationIterative" => ClosureEliminationIterativeTransformer
            case "ClosureEliminationLiu" => ClosureEliminationLiuTransformer
            case "ClosureEliminationSquare" => ClosureEliminationSquareTransformer
            case "ClosureEliminationVakili" => ClosureEliminationVakiliTransformer
            case "ClosureEliminationClaessen" => ClosureEliminationClaessenTransformer

            // Definitions
            case "AxiomatizeFuncDefn" => AxiomatizeFuncDefnTransformer

            // EnumerateFiniteValues
            case "DEsToDistinctConstants" => DEsToDistinctConstantsTransformer
            case "DEsToNonDistinctConstants" => DEsToNonDistinctConstantsTransformer
            case "DEsToEnums" => DEsToEnumsTransformer

            // Integers
            case "AxiomatizeIntPredDefns" => AxiomatizeIntPredDefnsTransformer
            case "IntToBV" => IntToBVTransformer
            case "IntNOBV" => IntNOBVTransformer
            case "IntOPFI" => IntOPFITransformer
            case "LiaCheck" => LiaCheckTransformer

            // Quantifiers
            case "AntiPrenex" => AntiPrenexTransformer
            case "MaxAlphaRenaming" => MaxAlphaRenamingTransformer
            case "QuantifiersToDefns" => QuantifiersToDefnsTransformer
            case "Skolemize" => SkolemizeTransformer

            // Scopes
            case "MaxUnboundedScopes" => MaxUnboundedScopesTransformer
            case "ScopeNonExactPredicates" => ScopeNonExactPredicatesTransformer

            // Simplify
            case "SimplifyConstantsNotDistinct" => SimplifyConstantsNotDistinctTransformer
            case "SimplifyLearnedLiterals" => SimplifyLearnedLiteralsTransformer
            case "Simplify" => SimplifyTransformer
            case "SimplifyWithRange" => SimplifyWithRangeTransformer
            case "SimplifyWithScalarQuantifiers" => SimplifyWithScalarQuantifiersTransformer
            case "SplitConjunction" => SplitConjunctionTransformer

            case _ => {
                Errors.API.transformerDoesNotExist(name)
                null
            }
        }
        checkName(name,t)
    }

    private def checkName(s:String, t:ProblemStateTransformer): ProblemStateTransformer = {
        Errors.Internal.assertion(t.name == s, s +" does not match "+ t.name)
        t        
    }
}
