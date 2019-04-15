package fortress.transformers

import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // By default use immutable Seq

import fortress.tfol._
import fortress.util.Errors

/** Replaces domain elements with distinct constants that simulate them.
  * This transformation is required before sending the theory to an SMT solver.
  */
class DomainEliminationTransformer(scopes: Map[Type, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Type, Integer]) = this({
        val scopes1: Map[Type, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory =  {
        Errors.precondition(!scopes.contains(Type.Bool))
        Errors.precondition(scopes.keySet subsetOf theory.types)
        Errors.precondition(scopes.values.forall(_ > 0))
        
        // Generate the constants that simulate the domain elements
        val domainConstantsMap: Map[Type, Seq[Var]] = for(
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
            (sort, domainConstantVars) <- domainConstantsMap
        ) yield Distinct(domainConstantVars)
        
        // Eliminate domain elements in existing axioms
        val convertedAxioms = theory.axioms.map(
            axiom => axiom.eliminateDomainElements
        )
        
        Theory.mkTheoryWithSignature(theory.signature)
            .withConstants(domainConstants)
            .withAxioms(distinctConstraints)
            .withAxioms(convertedAxioms)
    }
    
    override def getName: String = "Domain Elimination Transformer"
}
