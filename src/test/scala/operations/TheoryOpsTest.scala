import org.scalatest._

import fortress.msfol._
import fortress.operations.TheoryOps._

class TheoryOpsTest extends UnitSuite {

  val A = Sort.mkSortConst("A")
  val B = Sort.mkSortConst("B")

  val c = Var("c")
  val p = Var("p")
  val q = Var("q")
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
    baseTheory.sortCount should be(3)
  }

  test("function count") {
    baseTheory.functionCount should be(2)
  }

  test("predicate count") {
    baseTheory.predicateCount should be(1)
  }

  test("depth of quantification of simple terms") {
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

  test("depth of quantification for nested foralls and Exists") {
    val P = FuncDecl("P", A, Sort.Bool)
    val Q = FuncDecl("Q", B, Sort.Bool)
    val R = FuncDecl("R", A, B, Sort.Bool)
    val g = FuncDecl("g", A, A)

    val theory = Theory.empty
      .withSorts(A, B)
      .withFunctionDeclarations(P, Q, R, g)
      .withAxiom(Forall(
        x of A, (App("g", x) === x) or Forall(y of B, App("R", x, y) and Exists(p of A, Not(App("P", p))))
      ))

    theory.depthQuantification should be(3)
  }

  test("depth of nested functions") {
    val theory = baseTheory
      .withAxiom(Exists(x.of(A),
        Forall(y.of(A), Implication(Eq(x, App("f", y)), App("P", App("f", y), x))))
      )
      .withAxiom(Forall(x.of(A), Not(App("P", App("f", x), c))))

    theory.depthQuantification should be(2)
  }

}
