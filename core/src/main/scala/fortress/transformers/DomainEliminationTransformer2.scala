package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Introduces constants to simulate the domain elements, asserting these constants are
  * all distinct and replacing occurrences of domain elements with the appropriate constant.
  * Leaves other aspects of the Problem unchanged.
  *
  * This variant removes constraints asserting constants are distinct, thus implements the
  * "collapsing constants" approach for solving with non-exact scope.
  */
class DomainEliminationTransformer2 extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val domainElemsMap: Map[Sort, Seq[DomainElement]] =
                (for(sort <- theory.sorts if !sort.isBuiltin) yield {
                    val domElems = DomainElement.range(1 to scopes(sort).size, sort)
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
            val convertedAxioms = theory.axioms map (_.eliminateDomainElementsConstants)
            val convertedFunctionDefinitions = theory.signature.functionDefinitions.map (_.mapBody(_.eliminateDomainElementsConstants))
            val convertedConstantDefinitions = theory.signature.constantDefinitions.map(_.mapBody(_.eliminateDomainElementsConstants))

            
            val newTheory = theory.withoutAxioms
                .withConstantDeclarations(domainConstants)
                // .withAxioms(distinctConstraints)
                .withAxioms(convertedAxioms)
                .withoutConstantDefinitions
                .withConstantDefinitions(convertedConstantDefinitions)
                .withoutFunctionDefinitions
                .withFunctionDefinitions(convertedFunctionDefinitions)
            
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants = true)
        }
    }
    
    override def name: String = "Domain Elimination To Constants Transformer 2"
}
