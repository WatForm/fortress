import org.scalatest._

import fortress.msfol._
import fortress.operations.TheoryOps._

class TheoryOpsTest extends UnitSuite {

  val A = Sort.mkSortConst("A")
  val B = Sort.mkSortConst("B")

  val c = Var("c")
  val p = Var("p")
  val x = Var("x")
  val y = Var("y")

  val f = FuncDecl.mkFuncDecl("f", A, A)
  val P = FuncDecl.mkFuncDecl("P", A, A, Sort.Bool)

  val baseTheory = Theory.empty
    .withSort(A)
    .withSort(B)
    .withConstant(p.of(Sort.Bool))
    .withConstant(c.of(A))
    .withFunctionDeclaration(f)
    .withFunctionDeclaration(P)

  test("sort count") {
    baseTheory.sortCount should be(2)
  }

  test("function count") {
    baseTheory.functionCount should be(2)
  }

  test("predicate count") {
    baseTheory.predicateCount should be(1)
  }

  test("term count") {
    val theory = baseTheory
      .withAxiom(Forall(x.of(A),
        Iff(
          Implication(Eq(c, App("f", x)), App("P", App("f", x), c)),
          OrList(Top, Bottom)
        )
      ))
      .withAxiom(AndList(Exists(x.of(A), Not(App("P", App("f", x), c))), Bottom))

    theory.termCount should be(22)
  }

  test("maximum depth of quantification among all axioms") {
    val theory = baseTheory
      .withAxiom(Forall(x.of(A),
        Iff(
          Implication(Eq(c, App("f", x)), App("P", App("f", x), c)),
          OrList(Top, Bottom)
        )
      ))
      .withAxiom(AndList(Exists(x.of(A), Not(App("P", App("f", x), c))), Bottom))

    theory.depthQuantification should be(1)
  }

  test("maximum depth of nested functions among all axioms") {
    val theory = baseTheory
      .withAxiom(Exists(x.of(A),
        Forall(y.of(A), Implication(Eq(x, App("f", y)), App("P", App("f", y), x))))
      )
      .withAxiom(Forall(x.of(A), Not(App("P", App("f", x), c))))

    theory.depthQuantification should be(2)
  }

}