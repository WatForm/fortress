package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.modelfind.ProblemState

/** Instantiates quantifiers with domain elements, according to the scopes of the problem.
  * The scopes must provide sizes for all sorts in the theory.
  * The input theory is required to have no enum sorts.
  * The resulting theory's signature is identical to the original.
  * The scopes are not changed.
  * The resulting problem is equivalent to the original.
  */
  
// TODO it seems like we could remove the requirement to ahve no enum sorts or existential quantifiers
class QuantifierExpansionSimplifierTransformer private (useConstForDomElem: Boolean) extends ProblemStateTransformer {
    
    private def DE(index: Integer, sort: Sort): Term =
        if (useConstForDomElem) DomainElement(index, sort).asSmtConstant
        else DomainElement(index, sort)
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            Errors.precondition(scopes.keySet == theory.sorts.filter(!_.isBuiltin), scopes.keySet.toString)
        
            val domainElemsMap: Map[Sort, Seq[Term]] = scopes.map {
                case (sort, size) => (sort, for(i <- 1 to size) yield DE(i, sort))
            }
        
            val newAxioms = theory.axioms.map(
                axiom => axiom.expandQuantifiersAndSimplify(domainElemsMap)
            )
        
            val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp)
        }
    }
    
    override def name: String = "Quantifier Expansion Simplifier Transformer"
}

object QuantifierExpansionSimplifierTransformer {
    def create(): QuantifierExpansionSimplifierTransformer = new QuantifierExpansionSimplifierTransformer(false)
    def createWithDomElemsAsConstants(): QuantifierExpansionSimplifierTransformer = new QuantifierExpansionSimplifierTransformer(true)
}
