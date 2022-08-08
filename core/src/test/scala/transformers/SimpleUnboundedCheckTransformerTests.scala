import fortress.msfol._
import fortress.transformers._

class SimpleUnboundedCheckTransformerTests extends UnitSuite with CommonSymbols {
    val transformer = new TheoryApplication(new SimpleUnboundedCheckTransformer)

    val baseTheory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withSort(C)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from B to BoolSort)
            .withFunctionDeclaration(R from C to BoolSort)

    var scopes = Map.empty[Sort, Scope]

    test("filter quantified sorts") {
        val theory = baseTheory
                .withAxiom(Forall(x.of(A), App("P", x)))
                .withAxiom(Exists(x.of(B), App("Q", x)))

        scopes = scopes + (A -> ExactScope(1))
        scopes = scopes + (B -> ExactScope(1))
        scopes = scopes + (C -> ExactScope(1))

        var expected: Map[Sort, Scope] = Map.empty
        expected = expected + (A -> ExactScope(1))
        expected = expected + (B -> ExactScope(1))

        transformer(theory, scopes, "flag") should be (expected)
    }

    //TODO: we need more unit tests

}
