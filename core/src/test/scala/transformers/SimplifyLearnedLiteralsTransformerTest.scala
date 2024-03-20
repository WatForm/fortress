import fortress.msfol._
import fortress.transformers._
import fortress.problemstate.ProblemState

class SimplifyLearnedLiteralTransformerTest extends UnitSuite {

    val st = new SimplifyLearnedLiteralsTransformer

    def checkTransform(input: Theory, expected: Theory) = {
        val ps = ProblemState(input)
        st(ps).theory should equal (expected)
    }

    val A = Sort.mkSortConst("A")

    val x = Var("x")
    val y = Var("y")

    val f = FuncDecl.mkFuncDecl("f", A, A)
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)

    val baseTheory = Theory.empty
      .withSort(A)
      .withConstantDeclaration(x.of(A))
      .withConstantDeclaration(y.of(A))
      .withFunctionDeclaration(f)
      .withFunctionDeclaration(P)

    test("positive literal equals") {
        val theory = baseTheory
          .withAxiom(Eq(x, App("f", y)))
          .withAxiom(Or(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(Eq(x, App("f", y)))

        checkTransform(theory, expected)
    }

    test("negative literal equals") {
        val theory = baseTheory
          .withAxiom(Not(Eq(x, App("f", y))))
          .withAxiom(And(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(Not(Eq(x, App("f", y))))
          .withAxiom(Bottom)

        checkTransform(theory, expected)
    }

    test("positive literal app") {
        val theory = baseTheory
          .withAxiom(App("P", y))
          .withAxiom(And(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(App("P", y))
          .withAxiom(Eq(x, App("f", y)))

        checkTransform(theory, expected)
    }

    test("negative literal app") {
        val theory = baseTheory
          .withAxiom(Not(App("P", y)))
          .withAxiom(Or(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(Not(App("P", y)))
          .withAxiom(Eq(x, App("f", y)))

        checkTransform(theory, expected)
    }
}
