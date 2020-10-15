package fortress.msfol

// Syntax helpers for MSFOL Domain Specific Language in Scala

object DSL {
    implicit class DSLTerm(term: Term) {
        // Be aware if you chain this method together, you will get several nested AndLists
        def and(other: Term): Term = AndList(Seq(term, other))
        // Be aware if you chain this method together, you will get several nested OrLists
        def or(other: Term): Term = OrList(Seq(term, other))
        def ==>(other: Term): Term = Implication(term, other)
        def ===(other: Term): Term = Eq(term, other)
        def <==>(other: Term): Term = Iff(term, other)
        def unary_! : Term = Not(term)
    }

    case class FunctionalSymbol(name: String) {
        def apply(terms: Term*): Term = App(name, terms)

        def from(argSorts: Sort*): FunctionalSymbolWithArgSorts = FunctionalSymbolWithArgSorts(name, argSorts)
    }

    case class FunctionalSymbolWithArgSorts(name: String, argSorts: Seq[Sort]) {
        def to(resultSort: Sort): FuncDecl = FuncDecl(name, argSorts, resultSort)
    }
}