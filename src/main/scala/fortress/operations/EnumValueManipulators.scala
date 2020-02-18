package fortress.operations

import fortress.msfol._

case class EnumValueEliminator(eliminationMapping: Map[EnumValue, DomainElement]) extends NaturalTermRecursion {
    override val exceptionalMappings: PartialFunction[Term, Term] = {
        case e @ EnumValue(_) if (eliminationMapping contains e) => eliminationMapping(e)
    }
    
    def apply(term : Term): Term = naturalRecur(term)
}

object EnumValueAccumulator extends NaturalSetAccumulation[EnumValue] {
    override val exceptionalMappings: PartialFunction[Term, Set[EnumValue]] = {
        case e @ EnumValue(_) => Set(e)
    }
    
    def apply(term: Term): Set[EnumValue] = naturalRecur(term)
}
