package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import scala.collection.immutable.Seq

/** Instantiates quantifiers with domain elements, according to the provided scopes.
  * The scopes must provide sizes for all sorts in the theory.
  * The input theory is required to have no existential quantifiers and no enum sorts.
  * The resulting theory's signature is identical to the original.
  */
class DomainInstantiationTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Sort, Integer]) = this({
        val scopes1: Map[Sort, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = {
        Errors.precondition(!scopes.contains(BoolSort))
        Errors.precondition(scopes.keySet == theory.sorts.filter(!_.isBuiltin), scopes.keySet.toString)
        Errors.precondition(scopes.values.forall(_ > 0))
        
        val domainElemsMap: Map[Sort, Seq[Term]] = scopes.map {
            case (sort, size) => (sort, for(i <- 1 to size) yield DomainElement(i, sort))
        }
        
        val newAxioms = theory.axioms.map(
            axiom => axiom.recklessUnivInstantiate(domainElemsMap)
        )
        
        val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
        newTheory
    }
    
    override def name: String = "Domain Instantiation Transformer"
}
