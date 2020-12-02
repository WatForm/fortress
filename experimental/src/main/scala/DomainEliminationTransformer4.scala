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
class DomainEliminationTransformer4 extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            val domainElemsMap: Map[Sort, Seq[DomainElement]] =
                (for(sort <- theory.sorts if !sort.isBuiltin) yield {
                    val domElems = DomainElement.range(1 to scopes(sort), sort)
                    (sort, domElems)
                }).toMap
            
            val domainConstants: Iterable[AnnotatedVar] = domainElemsMap.values.flatten.map {
                de => de.asSmtConstant of de.sort
            }
            
            // Assert the constants are distinct
            // val distinctConstraints = for(
            //     (sort, domainElems) <- domainElemsMap if (domainElems.size > 1)
            // ) yield Distinct(domainElems map (_.asSmtConstant))
            
            // Eliminate domain elements in existing axioms
            val convertedAxioms = theory.axioms map (_.eliminateDomainElements)
            
            val newTheory = theory.withoutAxioms
                .withConstants(domainConstants)
                // .withAxioms(distinctConstraints)
                .withAxioms(convertedAxioms)
            
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp)
        }
    }
    
    override def name: String = "Domain Elimination Transformer 2"
}
