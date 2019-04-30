package fortress.tfol.operations

import fortress.tfol._

object EnumValueEliminator {
    def apply(term : Term, eliminationMapping: Map[EnumValue, DomainElement]): Term = {
        def recur(term: Term): Term = term match {
            case e @ EnumValue(_) if (eliminationMapping contains e) => eliminationMapping(e)
            case _ => term.naturalRecur(recur)
        }
        recur(term)
    }
}

object EnumValueAccumulator {
    def apply(term: Term): Set[EnumValue] = {
        def recur(term: Term): Set[EnumValue] = term match {
            case e @ EnumValue(_) => Set(e)
            case _ => term.naturalRecurSetAccumulate(recur)
        }
        recur(term)
    }
}
