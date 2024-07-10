import fortress.msfol._
import fortress.problemstate.ProblemState
import fortress.transformers.{MaxAlphaRenamingTransformer, NnfTransformer, SimplifyWithScalarQuantifiersTransformer,IfLiftingTransformer}

class SimplifyWithScalarQuantifiersTransformerTests extends UnitSuite with CommonSymbols {

    def simplify(th: Theory): Theory =
        SimplifyWithScalarQuantifiersTransformer(MaxAlphaRenamingTransformer(NnfTransformer(IfLiftingTransformer(ProblemState(th))))).theory

    test("nested quantifier") {
        val y0 = Var("y_0") // due to max alpha renaming

        val term = Forall(x of A, Or(P(x), Forall(y of A, Or(Q(x, y), !(x === f(y))))))
        val expected = Forall(y0 of A, Or(Q(f(y0), y0), P(f(y0))))

        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclarations(Q from (A, A) to BoolSort)
            .withAxiom(term)
        val expectedTheory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclarations(Q from (A, A) to BoolSort)
            .withAxiom(expected)
        simplify(theory) should be(expectedTheory)
    }

}
