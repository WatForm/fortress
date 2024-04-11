import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.symmetry.{DefaultSymmetryBreakerFactoryDL, LowArityFirstAndMostUsedOrderFactory}
import fortress.transformers._

class SymmetryBreakingTransformer_MostUsedTest extends UnitSuite {

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val d1 = Var("d1")
    val d2 = Var("d2")
    val d3 = Var("d3")
    val p = Var("p")
    val q = Var("q")

    test("constants") {
        val theory = Theory.empty
          .withSorts(A, B)
          .withConstantDeclarations(c1 of A, c2 of A, d1 of B)
          .withAxiom(Forall(x of A, x === c2))

        val expected = theory
          .withAxiom(c2 === DomainElement(1, A))
          .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
          .withAxiom((c1 === DomainElement(2, A)) ==> (c2 === DomainElement(1, A)))
          .withAxiom(d1 === DomainElement(1, B))

        val expectedRangeFormulas = Set(RangeRestriction(c2, Vector(DomainElement(1, A))), RangeRestriction(c1, Vector(DomainElement(1, A), DomainElement(2, A))), RangeRestriction(d1, Vector(DomainElement(1, B))))

        val scopes = Map(A -> ExactScope(2), B -> ExactScope(2))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        transformer(ProblemState(theory, scopes)) should be(ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true, haveRunNNF = true, verbose = false)))
    }
    test("constants_with_unbounded") {
        val theory = Theory.empty
                .withSorts(A, B)
                .withConstantDeclarations(c1 of A, c2 of A, d1 of B)
                .withAxiom(Forall(x of A, x === c2))

        val expected = theory
                .withAxiom(c2 === DomainElement(1, A))
                .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
                .withAxiom((c1 === DomainElement(2, A)) ==> (c2 === DomainElement(1, A)))
//                .withAxiom(d1 === DomainElement(1, B))

        val expectedRangeFormulas = Set(RangeRestriction(c2, Vector(DomainElement(1, A))), RangeRestriction(c1, Vector(DomainElement(1, A), DomainElement(2, A))))

        val scopes = Map(A -> ExactScope(2))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        transformer(ProblemState(theory, scopes)) should be(ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true, haveRunNNF = true, verbose = false)))
    }

    test("function arity 1") {
        val theory = Theory.empty
          .withSorts(A, B)
          .withConstantDeclarations(c1 of A, d1 of B)
          .withFunctionDeclaration(FuncDecl("f", A, B))
          .withFunctionDeclaration(FuncDecl("g", B, A))

        val expected = theory
          .withAxiom(Or(
              App("f", DomainElement(2, A)) === DomainElement(1, B),
              App("f", DomainElement(2, A)) === DomainElement(2, B),
              App("f", DomainElement(2, A)) === DomainElement(3, B)))
          .withAxiom(c1 === DomainElement(1, A))
          .withAxiom((App("f", DomainElement(2, A)) === DomainElement(3, B)) ==> (App("f", DomainElement(1, A)) === DomainElement(2, B)))
          .withAxiom(d1 === DomainElement(1, B))
          .withAxiom(Or(
              App("f", DomainElement(1, A)) === DomainElement(1, B),
              App("f", DomainElement(1, A)) === DomainElement(2, B)))
          .withAxiom(Or(
              App("g", DomainElement(1, B)) === DomainElement(1, A),
              App("g", DomainElement(1, B)) === DomainElement(2, A)))

        val expectedRangeFormulas = Set(RangeRestriction(App("g", DomainElement(1, B)), Vector(DomainElement(1, A), DomainElement(2, A))), RangeRestriction(d1, Vector(DomainElement(1, B))), RangeRestriction(App("f", DomainElement(2, A)), Vector(DomainElement(1, B), DomainElement(2, B), DomainElement(3, B))), RangeRestriction(c1, Vector(DomainElement(1, A))), RangeRestriction(App("f", DomainElement(1, A)), Vector(DomainElement(1, B), DomainElement(2, B))))

        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        transformer(ProblemState(theory, scopes)) should be(ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true, haveRunNNF = true, verbose = false)))
    }

    test("function arity 1 - with_unbounded") {
        val theory = Theory.empty
                .withSorts(A, B)
                .withConstantDeclarations(c1 of A, d1 of B)
                .withFunctionDeclaration(FuncDecl("f", A, B))
                .withFunctionDeclaration(FuncDecl("g", B, A))

        val expected = theory
                .withAxiom(c1 === DomainElement(1, A))

        val expectedRangeFormulas = Set(RangeRestriction(c1, Vector(DomainElement(1, A))))

        val scopes = Map(A -> ExactScope(2))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        transformer(ProblemState(theory, scopes)) should be(ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true, haveRunNNF = true, verbose = false)))
    }

    test("function arity 2") {
        val theory = Theory.empty
          .withSorts(A, B, C)
          .withConstantDeclaration(c1 of B)
          .withFunctionDeclaration(FuncDecl("f", A, B, C))
          .withFunctionDeclaration(FuncDecl("g", A, B, A, C))
          .withAxiom(Forall(x of A, App("f", x, c1) === App("g", x, c1, x)))

        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3), C -> ExactScope(2))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        val result = transformer(ProblemState(theory, scopes))
        result.theory.axioms.size should be(5)
        result.theory.axioms should contain(Forall(x of A, App("f", x, c1) === App("g", x, c1, x)))
        result.theory.axioms should contain(c1 === DomainElement(1, B))
        result.theory.axioms should contain(App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(1, C))
        result.theory.axioms should contain(Or(
            App("f", DomainElement(2, A), DomainElement(1, B)) === DomainElement(1, C),
            App("f", DomainElement(2, A), DomainElement(1, B)) === DomainElement(2, C)))
        result.theory.axioms should contain((App("f", DomainElement(2, A), DomainElement(1, B)) === DomainElement(2, C)) ==> (App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(1, C)))

        val expectedRangeFormulas = Set(RangeRestriction(c1, Vector(DomainElement(1, B))), RangeRestriction(App("f", DomainElement(1, A), DomainElement(1, B)), Vector(DomainElement(1, C))), RangeRestriction(App("f", DomainElement(2, A), DomainElement(1, B)), Vector(DomainElement(1, C), DomainElement(2, C))))
        result.rangeRestrictions should be(expectedRangeFormulas)
    }

    test("Multiple sorts with constants, functions and predicates") {
        val theory = Theory.empty
          .withSorts(A, B, C)
          .withConstantDeclaration(c1 of A)
          .withConstantDeclaration(c2 of B)
          .withConstantDeclaration(c3 of C)
          .withFunctionDeclaration(FuncDecl("f", A, B, C))
          .withFunctionDeclaration(FuncDecl("g", C, A))
          .withFunctionDeclaration(FuncDecl("h", B, B, BoolSort))
          .withAxiom(Forall(x of A, App("f", x, c2) === App("g", c3)))
          .withAxiom(App("h", c2, c2) === App("h", c2, c2))

        val scopes = Map(A -> ExactScope(4), B -> ExactScope(4), C -> ExactScope(4))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        val result = transformer(ProblemState(theory, scopes))

        result.theory.axioms.size should be(14)
        // Original axioms
        result.theory.axioms should contain(Forall(x of A, App("f", x, c2) === App("g", c3)))
        result.theory.axioms should contain(App("h", c2, c2) === App("h", c2, c2))
        // Symmetry breaking constraints for constants
        result.theory.axioms should contain(c1 === DomainElement(1, A))
        result.theory.axioms should contain(c2 === DomainElement(1, B))
        result.theory.axioms should contain(c3 === DomainElement(1, C))
        // Symmetry breaking constraints for function g
        result.theory.axioms should contain(Or(
            App("g", DomainElement(1, C)) === DomainElement(1, A),
            App("g", DomainElement(1, C)) === DomainElement(2, A)))
        result.theory.axioms should contain(Or(
            App("g", DomainElement(2, C)) === DomainElement(1, A),
            App("g", DomainElement(2, C)) === DomainElement(2, A),
            App("g", DomainElement(2, C)) === DomainElement(3, A)))
        result.theory.axioms should contain(Or(
            App("g", DomainElement(3, C)) === DomainElement(1, A),
            App("g", DomainElement(3, C)) === DomainElement(2, A),
            App("g", DomainElement(3, C)) === DomainElement(3, A),
            App("g", DomainElement(3, C)) === DomainElement(4, A)))

        result.theory.axioms should contain((App("g", DomainElement(2, C)) === DomainElement(3, A)) ==>
          (App("g", DomainElement(1, C)) === DomainElement(2, A)))
        result.theory.axioms should contain((App("g", DomainElement(3, C)) === DomainElement(4, A)) ==>
          (App("g", DomainElement(2, C)) === DomainElement(3, A)))
        result.theory.axioms should contain((App("g", DomainElement(3, C)) === DomainElement(3, A)) ==>
          Or(App("g", DomainElement(1, C)) === DomainElement(2, A), App("g", DomainElement(2, C)) === DomainElement(2, A)))

        // Symmetry breaking constraints for predicate h
        result.theory.axioms should contain(App("h", DomainElement(3, B), DomainElement(3, B)) ==> App("h", DomainElement(2, B), DomainElement(2, B)))
        result.theory.axioms should contain(App("h", DomainElement(4, B), DomainElement(4, B)) ==> App("h", DomainElement(3, B), DomainElement(3, B)))

        // Symmetry breaking constraints for function f
        result.theory.axioms should contain(Or(
            App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(1, C),
            App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(2, C),
            App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(3, C),
            App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(4, C)))
    }

    test("Multiple sorts with constants, functions and predicates - with unbounded sorts") {
        // leave sort C unbounded
        val theory = Theory.empty
                .withSorts(A, B, C)
                .withConstantDeclaration(c1 of A)
                .withConstantDeclaration(c2 of B)
                .withConstantDeclaration(c3 of C)
                .withFunctionDeclaration(FuncDecl("f", A, B, C))
                .withFunctionDeclaration(FuncDecl("g", C, A))
                .withFunctionDeclaration(FuncDecl("h", B, B, BoolSort))
                .withAxiom(Forall(x of A, App("f", x, c2) === App("g", c3)))
                .withAxiom(App("h", c2, c2) === App("h", c2, c2))

        val scopes = Map(A -> ExactScope(4), B -> ExactScope(4))
        val transformer = new SymmetryBreakingTransformer_MostUsed(LowArityFirstAndMostUsedOrderFactory, DefaultSymmetryBreakerFactoryDL(None))
        val result = transformer(ProblemState(theory, scopes))

        // Original axioms
        result.theory.axioms should contain(Forall(x of A, App("f", x, c2) === App("g", c3)))
        result.theory.axioms should contain(App("h", c2, c2) === App("h", c2, c2))
        // Symmetry breaking constraints for constants
        result.theory.axioms should contain(c1 === DomainElement(1, A))
        result.theory.axioms should contain(c2 === DomainElement(1, B))

        // Symmetry breaking constraints for predicate h
        result.theory.axioms should contain(App("h", DomainElement(3, B), DomainElement(3, B)) ==> App("h", DomainElement(2, B), DomainElement(2, B)))
        result.theory.axioms should contain(App("h", DomainElement(4, B), DomainElement(4, B)) ==> App("h", DomainElement(3, B), DomainElement(3, B)))
    }
}
