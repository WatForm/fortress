package fortress.transformers

import scala.collection.JavaConverters._
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
        
        // Generate the constants that simulate the domain elements
        val domainConstantsMap: Map[Sort, Seq[Var]] = for(
            (sort, size) <- scopes
        ) yield { 
            val domainElements = for(i <- 1 to size) yield { DomainElement(i, sort).asSmtConstant }
            (sort, domainElements)
        }
        
        val domainConstants = for(
            (sort, domainConstantVars) <- domainConstantsMap;
            variable <- domainConstantVars
        ) yield { variable of sort }
        
        // Assert the constants are distinct
        val distinctConstraints = for(
            (sort, domainConstantVars) <- domainConstantsMap if (domainConstantVars.size > 1)
        ) yield Distinct(domainConstantVars)
        
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
