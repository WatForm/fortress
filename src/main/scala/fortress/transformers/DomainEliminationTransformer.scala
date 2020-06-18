package fortress.transformers

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

/** Replaces occurences of domain elements in axioms with constants 
  * that simulate them, asserting that they are distinct.
  * Leaves all other aspects of the theory unchanged.
  */
class DomainEliminationTransformer extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  {
        val domainElements: Set[DomainElement] = theory.axioms.flatMap(_.domainElements)
        
        val domainConstants: Set[AnnotatedVar] = domainElements.map(de => de.asSmtConstant of de.sort)
        
        val domainElemsMap: Map[Sort, Seq[DomainElement]] = theory.sorts.map(sort => {
            val domElems = domainElements.filter(_.sort == sort).toSeq.sortWith(_.index < _.index) // Sort the domain elements for testing consistency
            (sort, domElems)
        }).toMap
        
        // Assert the constants are distinct
        val distinctConstraints = for(
            (sort, domainElems) <- domainElemsMap if (domainElems.size > 1)
        ) yield Distinct(domainElems.map(_.asSmtConstant))
        
        // Eliminate domain elements in existing axioms
        val convertedAxioms = theory.axioms.map(
            axiom => axiom.eliminateDomainElements
        )
        
        theory.withoutAxioms
            .withConstants(domainConstants)
            .withAxioms(distinctConstraints)
            .withAxioms(convertedAxioms)
    }
    
    override def name: String = "Domain Elimination Transformer"
}
