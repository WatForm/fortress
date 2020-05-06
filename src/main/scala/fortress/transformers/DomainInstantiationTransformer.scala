package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import scala.collection.immutable.Seq

/** Instantiates quantifiers with domain elements, according to the scopes of the problem.
  * The scopes must provide sizes for all sorts in the theory.
  * The input theory is required to have no existential quantifiers and no enum sorts.
  * The resulting theory's signature is identical to the original.
  * The scopes are not changed.
  */
  
// TODO it seems like we could remove the requirement to ahve no enum sorts or existential quantifiers
class DomainInstantiationTransformer extends ProblemTransformer {
    
    override def apply(problem: Problem): Problem = problem match {
        case Problem(theory, scopes) => {
            Errors.precondition(scopes.keySet == theory.sorts.filter(!_.isBuiltin), scopes.keySet.toString)
        
            val domainElemsMap: Map[Sort, Seq[Term]] = scopes.map {
                case (sort, size) => (sort, for(i <- 1 to size) yield DomainElement(i, sort))
            }
        
            val newAxioms = theory.axioms.map(
                axiom => axiom.recklessUnivInstantiate(domainElemsMap)
            )
        
            val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
            Problem(newTheory, scopes)
        }
    }
    
    override def name: String = "Domain Instantiation Transformer"
}
