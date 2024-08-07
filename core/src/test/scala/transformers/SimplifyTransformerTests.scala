import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate.ProblemState

class SimplifyTransformerTests extends UnitSuite {

    val st = SimplifyTransformer

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

    test("basic simplify") {
        val theory = baseTheory
          .withAxiom(Not(Not(Eq(x, App("f", y)))))
          .withAxiom(Or(Eq(x, App("f", y)), App("P", y), Top) <==> Top)

        val expected = baseTheory
          .withAxiom(Eq(x, App("f", y)))
          .withAxiom(Top)

        st(ProblemState(theory)).theory should be(expected)
    }
}
