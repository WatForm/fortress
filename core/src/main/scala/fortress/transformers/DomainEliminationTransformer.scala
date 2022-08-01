package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Introduces constants to simulate the domain elements, asserting these constants are
  * all distinct and repalacing occurrences of domain elements with the appropriate constant.
  * Leaves other aspects of the Problem unchanged.
  */
object DomainEliminationTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val domainElemsMap: Map[Sort, Seq[DomainElement]] =
                (for(sort <- theory.sorts if !sort.isBuiltin  && scopes.contains(sort)) yield {
                    val domElems = DomainElement.range(1 to scopes(sort).size, sort)
                    (sort, domElems)
                }).toMap
            
            val domainConstants: Iterable[AnnotatedVar] = domainElemsMap.values.flatten.map {
                de => de.asSmtConstant of de.sort
            }

            // Assert the constants are distinct
            val distinctConstraints = for(
                (sort, domainElems) <- domainElemsMap if (domainElems.size > 1)
            ) yield Distinct(domainElems map (_.asSmtConstant))
            
            // Eliminate domain elements in existing axioms
            val convertedAxioms = theory.axioms map (_.eliminateDomainElementsConstants)
            
            val newTheory = theory.withoutAxioms
                .withConstants(domainConstants)
                .withAxioms(distinctConstraints)
                .withAxioms(convertedAxioms)
            
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants = true)
        }
    }
    
    override def name: String = "Domain Elimination To Constants Transformer"
}
