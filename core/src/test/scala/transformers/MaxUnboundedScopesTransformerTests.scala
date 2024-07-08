import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class MaxUnboundedScopesTransformerTests extends UnitSuite with CommonSymbols {
    val transformer = new TheoryApplication(new MaxUnboundedScopesTransformer)

    val baseTheory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withSort(C)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from B to BoolSort)
            .withFunctionDeclaration(R from C to BoolSort)

    var scopes = Map.empty[Sort, Scope]

    scopes = scopes + (A -> ExactScope(1))
    scopes = scopes + (B -> ExactScope(1))
    scopes = scopes + (C -> ExactScope(1))

    test("filter quantified sorts0") {
        val theory = baseTheory
                .withAxiom(Forall(x.of(A), App("P", x)))
                .withAxiom(Exists(x.of(B), App("Q", x)))

        var expected: Map[Sort, Scope] = Map.empty
        expected = expected + (A -> ExactScope(1))

        transformer(theory, scopes, "flag") should be (expected)
    }
    //TODO: we need more unit tests

    test("filter quantified sorts1") {
        val theory = baseTheory
                .withAxiom(Forall( x of A, Forall( y of B, Or( And(App("f", x), App("P", y)) , Forall( z of C, And(App("P", y),App("Q", z)) ) ) ) ))

        var expected: Map[Sort, Scope] = Map.empty
        expected = expected + (A -> ExactScope(1))
        expected = expected + (B -> ExactScope(1))
        expected = expected + (C -> ExactScope(1))

        transformer(theory, scopes, "flag") should be (expected)
    }


    test("filter quantified sort2") {
        val theory = baseTheory
                .withAxiom(Exists(x of A, Exists(y of B, App("P", x) ==> App("Q", y))))
                .withAxiom(Forall(z of C, Not(App("P", z))))

        var expected: Map[Sort, Scope] = Map.empty
        expected = expected + (C -> ExactScope(1))
        transformer(theory, scopes, "flag") should be (expected)
    }
}
