import org.scalatest._

import fortress.msfol._
import fortress.operations.TermMetrics._

class TermMetricsTest extends UnitSuite {

  val A = Sort.mkSortConst("A")
  val B = Sort.mkSortConst("B")

  val c = Var("c")
  val p = Var("p")
  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

  val f = FuncDecl.mkFuncDecl("f", A, A)
  val P = FuncDecl.mkFuncDecl("P", A, A, Sort.Bool)

  test("simple depth of quantification") {
    val term1 = Forall(Seq(x.of(A), y.of(A)),
      Iff(
        Implication(Eq(c, App("f", x)), App("P", App("f", y), c)),
        OrList(Top, Bottom)
      )
    )
    val term2 = Exists(x.of(A),
      Forall(y.of(A), Implication(Eq(x, App("f", y)), App("P", App("f", y), x))))

    depthQuantification(term1) should be(1)
    depthQuantification(term2) should be(2)
  }

  test("depth of quantification of multivariable Forall and Exists") {
    val term1 = Forall(x.of(A), Forall(y.of(A),
      Implication(Eq(c, App("f", x)), App("P", App("f", x), c))
    ))
    val term2 = Exists(x.of(A), Exists(y.of(A),
        Implication(Eq(c, App("f", x)), App("P", App("f", x), c))
    ))
    val term3 = Forall(x.of(A), Exists(y.of(A), Forall(z.of(A),
      Implication(Eq(c, App("f", x)), App("P", App("f", x), c))
    )))

    depthQuantification(term1) should be(1)
    depthQuantification(term2) should be(1)
    depthQuantification(term3) should be(3)
  }

  test("depth of nested functions") {
    val term = Exists(x.of(A),
      Forall(y.of(A), Implication(Eq(x, App("f", y)), App("P", App("f", y), x))))

    depthNestedFunc(term) should be(2)
  }

  test("term Count") {
    val term = Forall(Seq(x.of(A), y.of(A)),
      Iff(
        Implication(Eq(c, App("f", x)), App("P", App("f", y), c)),
        OrList(Top, Bottom)
      )
    )

    termCount(term) should be(14)
  }
}
