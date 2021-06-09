package fortress.msfol

import fortress.operations.TermOps._
import fortress.util.Errors

/** Represents a constraint that a term must evaluate to one of the given possible values.
  * 
  * @param term the term whose value is constrained
  * @param values the only possible values for the term to take
  */
case class RangeRestriction(term: Term, values: Seq[DomainElement]) {
    Errors.Internal.precondition(values.nonEmpty)
    Errors.Internal.precondition(values.distinct == values)
    Errors.Internal.precondition(values forall (de => de.sort == values.head.sort))
    
    val sort = values.head.sort
    
    /** Represents the range restriction as a formula using a simple disjunction. */
    def asFormula: Term = term equalsOneOf values
    
    /** Represents the range restriction as a formula saying that the term cannot be equal to
      * a value not present in the range restriction.
      *
      * @param allValues all the values a term of this sort could take (including ones not allowed by this range restriction)
      * @return a formula saying the term cannot equal anything in allValues that is not in the range restriction
      */
    def asNeqs(allValues: Seq[DomainElement]): Seq[Term] = {
        val invalidValues = allValues diff values
        invalidValues map (v => Not(Eq(term, v)))
    }
}
