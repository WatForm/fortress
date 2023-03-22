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
            var newSig = theory.signature
                .withConstantDeclarations(domainConstants)

            // We only remove a definition before readding it so all its dependencies are in the sig
            // definitions are basically untested
            for(cDef <- theory.signature.constantDefinitions){
                newSig = newSig.withoutConstantDefinition(cDef)
                newSig = newSig.withConstantDefinition(cDef.mapBody(_.eliminateDomainElementsEnums))
            }
            for(fDef <- theory.signature.functionDefinitions){
                newSig = newSig.withoutFunctionDefinition(fDef)
                newSig = newSig.withFunctionDefinition(fDef.mapBody(_.eliminateDomainElementsEnums))
            }

            val newTheory = Theory(newSig, convertedAxioms)
            
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants = true)
        }
    }
    
    override def name: String = "Domain Elimination To Constants Transformer 2"
}
