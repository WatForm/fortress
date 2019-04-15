package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._
import fortress.util.Errors

/** Instantiates quantifiers with all domain elements.
  * This transformation is parameterized by scopes mapping types to sizes.
  * The input theory is required to have no existential quantifiers.
  */
class DomainInstantiationTransformer(scopes: Map[Type, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Type, Integer]) = this({
        val scopes1: Map[Type, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = {
        Errors.precondition(!scopes.contains(Type.Bool))
        Errors.precondition(scopes.keySet subsetOf theory.types)
        Errors.precondition(scopes.values.forall(_ > 0))
        
        val domainElemsMap: Map[Type, Seq[Term]] = scopes.map {
            case (sort, size) => (sort, for(i <- 1 to size) yield DomainElement(i, sort))
        }
        
        val domainElemsMapJava: java.util.Map[Type, java.util.List[Term]] = domainElemsMap.map{
            case (sort, domainElems) => (sort, domainElems.asJava)
        }.asJava
        
        val newAxioms = theory.axioms.map(
            axiom => axiom.recklessUnivInstantiate(domainElemsMapJava)
        )
        
        val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
        newTheory
    }
    
    override def getName: String = "Domain Instantiation Transformer"
}
