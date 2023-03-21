import fortress.msfol._
import fortress.transformers._

class SimplifyLearnedLiteralTransformerTest extends UnitSuite {

    val st = new SimplifyLearnedLiteralsTransformer

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

        st(theory) should be(expected)
    }

    test("negative literal equals") {
        val theory = baseTheory
          .withAxiom(Not(Eq(x, App("f", y))))
          .withAxiom(And(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(Not(Eq(x, App("f", y))))
          .withAxiom(Bottom)

        st(theory) should be(expected)
    }

    test("positive literal app") {
        val theory = baseTheory
          .withAxiom(App("P", y))
          .withAxiom(And(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(App("P", y))
          .withAxiom(Eq(x, App("f", y)))

        st(theory) should be(expected)
    }

    test("negative literal app") {
        val theory = baseTheory
          .withAxiom(Not(App("P", y)))
          .withAxiom(Or(Eq(x, App("f", y)), App("P", y)))

        val expected = baseTheory
          .withAxiom(Not(App("P", y)))
          .withAxiom(Eq(x, App("f", y)))

        st(theory) should be(expected)
    }
}
