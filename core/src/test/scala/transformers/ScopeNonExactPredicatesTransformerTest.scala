import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._


class ScopeNonExactPredicatesTransformerTest extends UnitSuite with CommonSymbols {

    def transformer(p:ProblemState) = ScopeNonExactPredicatesTransformer(TypecheckSanitizeTransformer(p))

    val baseTheory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from B to BoolSort)

    var scopes = Map.empty[Sort, Scope]

    test("do nothing to all-exact-scope theory") {
        val theory = baseTheory
                .withAxiom(Not(Exists(x.of(A), App("P", x))))
                .withAxiom(Forall(x.of(A), Not(App("P", x))))

        val expected = baseTheory
                .withAxiom(Not(Exists(x.of(A), App("P", x))))
                .withAxiom(Forall(x.of(A), Not(App("P", x))))

        scopes = scopes + (A -> ExactScope(3))
        scopes = scopes + (B -> ExactScope(3))

        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected,scopes))

    }

    test("simple test0") {
        val theory = baseTheory
                .withAxiom(Not(Exists(x.of(A), App("P", x))))
                .withAxiom(Forall(x.of(A), Not(App("P", x))))

        val __Pred_A = FunctionSymbol("__@Pred_A")
        val __Pred_B = FunctionSymbol("__@Pred_B")

        val expected = baseTheory
                .withFunctionDeclaration(__Pred_A from A to BoolSort)
                .withFunctionDeclaration(__Pred_B from B to BoolSort)
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                .withAxiom(Exists(x.of(B), App("__@Pred_B", x)))
                .withAxiom(Not(Exists(x.of(A),And(App("__@Pred_A", x),App("P", x)))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Not(App("P", x)))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> NonExactScope(3))

        var newscopes = Map.empty[Sort, Scope]
        newscopes = newscopes + (A -> ExactScope(3)) + (B -> ExactScope(3))

        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, newscopes))

    }

    test("simple test1") {
        val theory = baseTheory
                .withAxiom(Forall(x.of(A), Forall(y.of(B), Or(App("P", x), App("Q", y)))))
                .withAxiom(Forall(x.of(A), Exists(y.of(B), And(App("P", x), App("Q", y)))))

        val __Pred_A = FunctionSymbol("__@Pred_A")
        val __Pred_B = FunctionSymbol("__@Pred_B")

        val expected = baseTheory
                .withFunctionDeclaration(__Pred_A from A to BoolSort)
                .withFunctionDeclaration(__Pred_B from B to BoolSort)
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                .withAxiom(Exists(x.of(B), App("__@Pred_B", x)))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x), Forall(y.of(B), Implication(App("__@Pred_B", y), Or(App("P", x), App("Q", y)))))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Exists(y.of(B), And(App("__@Pred_B", y),And(App("P", x), App("Q", y)))))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> NonExactScope(3))

                //println("theory: " + theory.toString)
                //println("result: " + transformer(theory, scopes).toString)

        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected))

    }

    test("test mixed scope") {
        val theory = baseTheory
                .withAxiom(Forall(x.of(A), Forall(y.of(B), Or(App("P", x), App("Q", y)))))
                .withAxiom(Forall(x.of(A), Exists(y.of(B), And(App("P", x), App("Q", y)))))

        val __Pred_A = FunctionSymbol("__@Pred_A")

        val expected = baseTheory
                .withFunctionDeclaration(__Pred_A from A to BoolSort)
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x), Forall(y.of(B), Or(App("P", x), App("Q", y))))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Exists(y.of(B), And(App("P", x), App("Q", y))))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> ExactScope(3))

        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected))


    }


}
