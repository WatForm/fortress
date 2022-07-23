package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Introduces enum values to simulate the domain elements, replacing occurrences
  * of domain elements with the appropriate constant. Leaves other aspects of the
  * Problem unchanged.
  */
object DatatypeTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val enumValuesMap: Map[Sort, Seq[EnumValue]] =
                (for (sort <- theory.sorts if !sort.isBuiltin && scopes.contains(sort)) yield {
                    val enumValues = DomainElement.range(1 to scopes(sort)._1, sort).map(_.asEnumValue)
                    (sort, enumValues)
                }).toMap

            // Convert domain elements in existing axioms to enum values
            val convertedAxioms = theory.axioms map (_.eliminateDomainElementsEnums)

            var newTheory = theory.withoutAxioms
              .withAxioms(convertedAxioms)

            newTheory = enumValuesMap.foldLeft(newTheory) {
                case (t, (s, enumValueSeq)) => t.withEnumSort(s, enumValueSeq: _*)
            }

            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants = false)
        }
    }

    override def name: String = "Domain Elimination To Enums Transformer"
}
