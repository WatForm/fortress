package fortress.msfol

import fortress.operations.TermOps._
import fortress.util.Errors

case class RangeRestriction(term: Term, values: Seq[DomainElement]) {
    Errors.precondition(values.nonEmpty)
    
    def asFormula: Term = term equalsOneOf values
}
