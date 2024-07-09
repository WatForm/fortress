package fortress.config

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
import scala.collection.mutable.ListBuffer
import fortress.config.ConfigOption

// A collection of options to use with a Manager in fortress.config.Manager

case object TypecheckSanitizeOption extends ToggleOption(
    "TypecheckSanitize",
    _.addTransformer(TypecheckSanitizeTransformer),
)

case object EnumEliminationOption extends ToggleOption(
    "EnumElimination",
    _.addTransformer(EnumEliminationTransformer)
)

case object NnfOption extends ToggleOption(
    "Nnf",
    _.addTransformer(NnfTransformer)
)

case object SkolemizeOption extends ToggleOption(
    "Skolemize",
    _.addTransformer(SkolemizeTransformer)
)

case object QuantifierExpansionOption extends ToggleOption(
    "QuantifierExpansion",
    _.addTransformer(QuantifierExpansionTransformer)
)

case object RangeFormulaOption extends ToggleOption(
    "RangeFormula",
    _.addTransformer(RangeFormulaUseDEsTransformer)
)

case object SimplifyOption extends ToggleOption(
    "Simplify",
    _.addTransformer(SimplifyTransformer)
)

case object DatatypeOption extends ToggleOption(
    "Datatypes",
    _.addTransformer(DEsAsDatatypeTransformer)
)


// Closures
case object ClosureEliminationOption extends ToggleOption(
    "ClosureElimination",
    _.addTransformer(ClosureEliminationIterativeTransformer)
)

case class SimpleOption(optName: String, transformer: ProblemStateTransformer) extends ToggleOption(
    optName,
    _.addTransformer(transformer)
)

/*
 * Symmetry Breaking
 */
