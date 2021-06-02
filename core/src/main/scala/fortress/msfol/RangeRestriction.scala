package fortress.msfol

import fortress.operations.TermOps._
import fortress.util.Errors

case class RangeRestriction(term: Term, values: Seq[DomainElement]) {
    Errors.Internal.precondition(values.nonEmpty)
    Errors.Internal.precondition(values.distinct == values)
    Errors.Internal.precondition(values forall (de => de.sort == values.head.sort))
    
    val sort = values.head.sort
    
    def asFormula: Term = term equalsOneOf values
    
    def asNeqs(allPossibleValues: Seq[DomainElement]): Seq[Term] = {
        val invalidValues = allPossibleValues diff values
        invalidValues map (v => Not(Eq(term, v)))
    }
}