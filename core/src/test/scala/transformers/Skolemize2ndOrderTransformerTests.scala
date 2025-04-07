import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate._
import fortress.msfol.Sort.Bool

class Skolemize2ndOrderTransformerTests extends UnitSuite with CommonSymbols {
    def skolemizer(th: Theory): ProblemState = Skolemize2ndOrderOnlyTransformer(TypecheckSanitizeTransformer(ProblemState(th)))


    val _a = Var("a")
    val _b = Var("b")

    val sk_0 = FunctionSymbol("sk_0")
    val sk_1 = FunctionSymbol("sk_1")
    val sk_2 = FunctionSymbol("sk_2")
    val sk_3 = FunctionSymbol("sk_3")
    val sk_4 = FunctionSymbol("sk_4")
    val sk_5 = FunctionSymbol("sk_5")
    val sk_6 = FunctionSymbol("sk_6")

    val x_0 = Var("x_0")

    test("Exists2ndOrder basic") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to B)
            .withConstantDeclaration(y of A)
            .withAxiom(Exists2ndOrder(R from B to BoolSort, R(P(y))))

        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to B)
            .withConstantDeclaration(y of A)
            .withFunctionDeclaration(sk_0 from B to BoolSort)
            .withAxiom(sk_0(P(y)))

        (skolemizer(theory).theory) should be (expected)
    }

    test("Forall Exists2ndOrder ") {
        val ax1 = Forall(y of A, Exists2ndOrder(R from B to BoolSort, R(P(y))))
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to B)
            .withAxiom(ax1)

        val ax2 = Forall(y of A, sk_0(P(y), y))
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to B)
            .withFunctionDeclaration(sk_0 from (B, A) to BoolSort)
            .withAxiom(ax2)

        (skolemizer(theory).theory) should be (expected)
    }

    test("nested Exists2ndOrder and forall") {
        val ax1 = Forall(x of A, Exists2ndOrder(R from B to BoolSort, Forall(y of B, Exists2ndOrder(f from (B, A) to B, R(f(y, x))))))
        val theory = Theory.empty
            .withSorts(A, B)
            .withAxiom(ax1)
        
        val ax2 = Forall(x of A, Forall(y of B, sk_0(sk_1(y, x, y, x), x)))
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(sk_0 from (B, A) to BoolSort)
            .withFunctionDeclaration(sk_1 from (B, A, B, A) to B)
            .withAxiom(ax2)
        
        (skolemizer(theory).theory) should be (expected)
    }

    test("multivariable Exists2ndOrder") {
        val ax1 = Forall(Seq(x of A, y of B), Exists2ndOrder(Seq(R from B to BoolSort, f from A to B), R(f(x))))
        val theory = Theory.empty
            .withSorts(A, B)
            .withAxiom(ax1)
        
        val ax2 = Forall(Seq(x of A, y of B), sk_0(sk_1(x, x), x))
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(sk_0 from (B, A) to BoolSort)
            .withFunctionDeclaration(sk_1 from (A, A) to B)
            .withAxiom(ax2)
        
        (skolemizer(theory).theory) should be (expected)
    }

    test("shadowing forall exists2ndOrder forall") {
        val ax1 = Forall(x of B, Exists2ndOrder(f from B to A, Q(x) and R(f(x)) and Forall(x of B, P(x, f(x)))))

        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(Q from B to BoolSort)
            .withFunctionDeclaration(R from A to BoolSort)
            .withFunctionDeclaration(P from (B, A) to BoolSort)
            .withAxiom(ax1)
        
        val ax2 = Forall(x of B, Q(x) and R(sk_0(x, x)) and Forall(x_0 of B, P(x_0, sk_0(x_0, x))))
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(Q from B to BoolSort)
            .withFunctionDeclaration(R from A to BoolSort)
            .withFunctionDeclaration(P from (B, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from (B, B) to A)
            .withAxiom(ax2)

        (skolemizer(theory).theory) should be (expected)
    }

    test("exists2ndorder with Closure") {
        val ax1 = Forall(x of C, Exists2ndOrder(P from (A, A, C, B) to BoolSort, Closure(P.name, y, z, Seq(x, w)) and ReflexiveClosure(P.name, z, y, Seq(x, w))))

        val theory = Theory.empty
            .withSorts(A, B, C)
            .withConstantDeclarations(y of A, z of A, w of B)
            .withAxiom(ax1)

        val ax2 = Forall(x of C, Closure(sk_0.name, y, z, Seq(x, w, x)) and ReflexiveClosure(sk_0.name, z, y, Seq(x, w, x)))

        val expected = Theory.empty
            .withSorts(A, B, C)
            .withConstantDeclarations(y of A, z of A, w of B)
            .withFunctionDeclaration(sk_0 from (A, A, C, B, C) to BoolSort)
            .withAxiom(ax2)

        (skolemizer(theory).theory) should be (expected)
    }
}
