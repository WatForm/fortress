import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._


class ScopeNonExactPredicatesTransformerTests extends UnitSuite with CommonSymbols {

    def typechecker(p:ProblemState) = TypecheckSanitizeTransformer(p)
    def transformer(p:ProblemState) = ScopeNonExactPredicatesTransformer(typechecker(p))

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

        // does not check problem state changes,
        // i.e., that the scopes are now set to Exact 
        // and that there is an unapply function
        transformer(ProblemState(theory, scopes)).theory should be (typechecker(ProblemState(expected,scopes)).theory)

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
                /* 2024-04-11
                   anti-vacuity axioms are no longer included for Non-Exact Scopes
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                .withAxiom(Exists(x.of(B), App("__@Pred_B", x)))
                */
                .withAxiom(Not(Exists(x.of(A),And(App("__@Pred_A", x),App("P", x)))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Not(App("P", x)))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> NonExactScope(3))

        var newscopes = Map.empty[Sort, Scope]
        newscopes = newscopes + (A -> ExactScope(3)) + (B -> ExactScope(3))

        // does not check problem state changes,
        // i.e., that the scopes are now set to Exact 
        // and that there is an unapply function
        transformer(ProblemState(theory, scopes)).theory should be (typechecker(ProblemState(expected, newscopes)).theory)

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
                /* 2024-04-11
                   anti-vacuity axioms are no longer included for Non-Exact Scopes
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                .withAxiom(Exists(x.of(B), App("__@Pred_B", x)))
                */
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x), Forall(y.of(B), Implication(App("__@Pred_B", y), Or(App("P", x), App("Q", y)))))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Exists(y.of(B), And(App("__@Pred_B", y),And(App("P", x), App("Q", y)))))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> NonExactScope(3))

                //println("theory: " + theory.toString)
                //println("result: " + transformer(theory, scopes).toString)

        // does not check problem state changes,
        // i.e., that the scopes are now set to Exact 
        // and that there is an unapply function
        transformer(ProblemState(theory, scopes)).theory should be (typechecker(ProblemState(expected,scopes)).theory)

    }

    test("test mixed scope") {
        val theory = baseTheory
                .withAxiom(Forall(x.of(A), Forall(y.of(B), Or(App("P", x), App("Q", y)))))
                .withAxiom(Forall(x.of(A), Exists(y.of(B), And(App("P", x), App("Q", y)))))

        val __Pred_A = FunctionSymbol("__@Pred_A")

        val expected = baseTheory
                .withFunctionDeclaration(__Pred_A from A to BoolSort)
                /* 2024-04-11
                   anti-vacuity axioms are no longer included for Non-Exact Scopes
                .withAxiom(Exists(x.of(A), App("__@Pred_A", x)))
                */
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x), Forall(y.of(B), Or(App("P", x), App("Q", y))))))
                .withAxiom(Forall(x.of(A), Implication(App("__@Pred_A", x),Exists(y.of(B), And(App("P", x), App("Q", y))))))

        scopes = scopes + (A -> NonExactScope(3))
        scopes = scopes + (B -> ExactScope(3))

        // does not check problem state changes,
        // i.e., that the scopes are now set to Exact 
        // and that there is an unapply function
        transformer(ProblemState(theory, scopes)).theory should be (typechecker(ProblemState(expected,scopes)).theory)


    }


}
