import org.scalatest._
import fortress.msfol._
import fortress.operations.TheoryOps._

import scala.collection.mutable

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
      .withConstantDeclaration(p.of(Sort.Bool))
      .withConstantDeclaration(c.of(A))
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

    test("maximum arity of functions") {
        val emptyTheory = Theory.empty

        emptyTheory.maxFunctionArity should be(0)
        baseTheory.maxFunctionArity should be(2)
    }

    test("boolean sort function args count") {
        val q = FuncDecl.mkFuncDecl("q", Sort.Bool, Sort.Bool, Sort.Bool)
        val t = FuncDecl.mkFuncDecl("t", Sort.Bool, A)
        val theory = baseTheory.withFunctionDeclaration(q)
          .withFunctionDeclaration(t)

        baseTheory.boolArgCount should be(0)
        theory.boolArgCount should be(3)
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

    test("Sort Inference metrics: new sorts inferred") {
        val f = FuncDecl("f", A, A, A)

        val theory = Theory.empty
          .withSorts(A)
          .withFunctionDeclarations(f)

        theory.inferSortsCount should be(2)
        theory.newSortsInferred should be(true)
    }

    test("most used declarations: counting occurrences correctly") {
        val theory = baseTheory
          .withAxiom(Forall(x.of(A),
              Iff(
                  Implication(Eq(c, App("f", x)), App("P", App("f", x), c)),
                  OrList(Top, Bottom)
              )
          ))
          .withAxiom(AndList(Exists(x.of(A), Not(App("P", App("f", x), c))), Bottom))

        val result = theory.mostUsedDeclarations
        val expected = Map(
            FuncDecl("P", A, A, BoolSort) -> 2,
            FuncDecl("f", A, A) -> 3,
            AnnotatedVar(Var("c"), A) -> 3,
            AnnotatedVar(Var("p"), BoolSort) -> 0)

        result should be(expected)
    }
}
