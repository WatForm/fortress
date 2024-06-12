package fortress.operations

import fortress.msfol._
object PortusPatternAccumulator {

    private def obeysPattern(term: Term): Boolean = {
        // TODO: in the future:
        //   Recognize sums of definitions called with all possible combinations of domain elements in some positions
        //   and possibly with non-domain-elements in others.
        // For now, recognize sums of definitions with the name Portus uses for its sum definitions.

        def extractAddends(sum: Term): Set[Term] = sum match {
            case BuiltinApp(IntPlus, args) => (args map extractAddends) reduce (_ union _)
            case term => Set(term)
        }
        val addends = extractAddends(term)

        def isSumDef(t: Term) = t match {
            case App(fname, _) => fname.startsWith("sum_def")
            case _ => false
        }
        addends.forall(isSumDef)
    }

    private object DomainElementAccumulator extends NaturalSetAccumulation[DomainElement] {
        override val exceptionalMappings: PartialFunction[Term, Set[DomainElement]] = {
            case de @ DomainElement(_, _) => Set(de)
            case term if obeysPattern(term) => Set() // ignore those that obey the pattern
        }

        def apply(term: Term): Set[DomainElement] = naturalRecur(term)
    }

    def domainElementsExceptPatternIn(term: Term): Set[DomainElement] = DomainElementAccumulator(term)

}
