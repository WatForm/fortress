package fortress.transformers

import scala.jdk.CollectionConverters._
import scala.collection.immutable.Seq // By default use immutable Seq

import fortress.msfol._
import fortress.util.Errors

/** Replaces occurences of domain elements in axioms with distinct constants 
  * that simulate them.
  * Leaves all other aspects of the theory unchanged.
  */
class DomainEliminationTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Sort, Integer]) = this({
        val scopes1: Map[Sort, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory =  {
        Errors.precondition(!scopes.contains(BoolSort))
        Errors.precondition(scopes.keySet subsetOf theory.sorts)
        Errors.precondition(scopes.values.forall(_ > 0))
        
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
