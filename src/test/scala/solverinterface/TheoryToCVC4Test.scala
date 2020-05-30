import org.scalatest._

import fortress.solverinterface.TheoryToCVC4
import fortress.msfol._

class TheoryToCVC4Test extends UnitSuite {
    test("simple theory test") {
        val theory: Theory = Theory.empty
            .withAxiom(Term.mkTop)
        assert(theory != null)

        val converter: TheoryToCVC4 = new TheoryToCVC4(theory)
        assert(converter.convert != null)
    }
}
