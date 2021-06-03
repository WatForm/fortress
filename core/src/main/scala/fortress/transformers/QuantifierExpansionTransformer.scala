package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._

/** Instantiates quantifiers with domain elements, according to the scopes of the problem.
  * The scopes must provide sizes for all sorts in the theory.
  * The input theory is required to have no enum sorts.
  * The scopes are not changed.
  */
object StandardQuantifierExpansionTransformer extends QuantifierExpansionTransformer(false, false)

// TODO it seems like we could remove the requirement to have no enum sorts or existential quantifiers

/** Instantiates quantifiers with domain elements, according to the scopes of the problem.
  * The scopes must provide sizes for all sorts in the theory.
  * The input theory is required to have no enum sorts.
  * The scopes are not changed.
  * @param useConstForDomElem if true, inserts domain elements as constants; if false, inserts domain elements directly (should be defaulted to false)
  * @param useSimplification if true, simplifies subformulas when expanding quantifiers; otherwise, does not (should be defaulted to false)
  */
private[transformers] class QuantifierExpansionTransformer (useConstForDomElem: Boolean, useSimplification: Boolean) extends ProblemStateTransformer {
    
    private def DE(index: Integer, sort: Sort): Term =
        if (useConstForDomElem) DomainElement(index, sort).asSmtConstant
        else DomainElement(index, sort)
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            Errors.Internal.precondition(scopes.keySet == theory.sorts.filter(!_.isBuiltin), scopes.keySet.toString)
        
            val domainElemsMap: Map[Sort, Seq[Term]] = scopes.map {
                case (sort, size) => (sort, for(i <- 1 to size) yield DE(i, sort))
            }
        
            val newAxioms = {
                if(useSimplification) theory.axioms.map(axiom => axiom.expandQuantifiersAndSimplify(domainElemsMap))
                else theory.axioms.map(axiom => axiom.expandQuantifiers(domainElemsMap))
            }
        
            val newTheory = Theory.mkTheoryWithSignature(theory.signature).withAxioms(newAxioms)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp)
        }
    }

    private val configStr1 = s"${if(useConstForDomElem) "Constants" else "-"}"
    private val configStr2 = s"${if(useSimplification) "Simplification" else "-"}"
    
    override def name: String = s"Quantifier Expansion Transformer ($configStr1, $configStr2)"
}
