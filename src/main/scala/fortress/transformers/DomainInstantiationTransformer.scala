package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._
import fortress.util.Errors

/** Instantiates quantifiers with domain elements.
  * Scoped sorts within the theory are expanded.
  * More scopes can be provided in addition to the ones in the theory.
  * The theory's scopes, together with the additional scopes, must provide
  * sizes for all sorts in the theory.
  * The input theory is required to have no existential quantifiers and no enum sorts.
  * The resulting theory has no scopes, though its signature is unchanged.
  */
class DomainInstantiationTransformer(additionalScopes: Map[Sort, Int]) extends TheoryTransformer {
    
    // Ugly conversion from Java data structures
    def this(additionalScopes: java.util.Map[Sort, Integer]) = this({
        val scopes1: Map[Sort, Integer] = additionalScopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = {
        Errors.precondition(fortress.util.Maps.noConflict(additionalScopes, theory.scopes))
        val scopes = additionalScopes ++ theory.scopes
        Errors.precondition(!scopes.contains(BoolSort))
        Errors.precondition(scopes.keySet == theory.sorts.filter(!_.isBuiltin), scopes.keySet.toString)
        Errors.precondition(scopes.values.forall(_ > 0))
        
        val domainElemsMap: Map[Sort, Seq[Term]] = scopes.map {
            case (sort, size) => (sort, for(i <- 1 to size) yield DomainElement(i, sort))
        }
        
        val domainElemsMapJava: java.util.Map[Sort, java.util.List[Term]] = domainElemsMap.map{
            case (sort, domainElems) => (sort, domainElems.asJava)
        }.asJava
        
        val newAxioms = theory.axioms.map(
            axiom => axiom.recklessUnivInstantiate(domainElemsMapJava)
        )
        
        val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
        newTheory
    }
    
    override def name: String = "Domain Instantiation Transformer"
}
