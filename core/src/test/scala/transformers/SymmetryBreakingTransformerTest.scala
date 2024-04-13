import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.symmetry.{DefaultSymmetryBreakerFactoryDL, LowArityFirstAndMostUsedOrderFactory}
import fortress.transformers._
import fortress.symmetry._

class SymmetryBreakingTransformerTest extends UnitSuite {

    val typechecker = TypecheckSanitizeTransformer

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
    
    val f = FuncDecl("f", A, B)
    val g = FuncDecl("g", A, A)
    val P = FuncDecl("P", C, BoolSort)

    test("basic test") {
        val theory = Theory.empty
          .withSorts(A, B, C)
          .withConstantDeclarations(c1 of A, c2 of A, d1 of B)
          .withFunctionDeclaration(g)
          .withFunctionDeclaration(P)
          .withAxiom(Forall(x of A, x === c2))

        val scopes = Map(A -> ExactScope(4), B -> ExactScope(3), C -> ExactScope(2))

        val expected = theory
          .withAxiom(c1 === DomainElement(1, A))
          .withAxiom((c2 === DomainElement(1, A)) or (c2 === DomainElement(2, A)))
          .withAxiom((c2 === DomainElement(2, A)) ==> (c1 === DomainElement(1, A)))
          .withAxiom(d1 === DomainElement(1, B))
          .withAxiom(OrList(for(i <- 1 to 3) yield {App("g", DomainElement(1, A)) === DomainElement(i, A) }))
          .withAxiom(OrList(for(i <- 1 to 4) yield {App("g", DomainElement(2, A)) === DomainElement(i, A) }))
          .withAxiom(App("P", DomainElement(2, C)) ==> App("P", DomainElement(1, C)))

        val expectedRangeFormulas = Set(
          RangeRestriction(c1, Seq(DomainElement(1, A))),
          RangeRestriction(c2, Seq(DomainElement(1, A), DomainElement(2, A))),
          RangeRestriction(d1, Seq(DomainElement(1, B))),
          RangeRestriction(App("g", DomainElement(1, A)), Seq(DomainElement(1, A), DomainElement(2, A), DomainElement(3, A))),
          RangeRestriction(App("g", DomainElement(2, A)), Seq(DomainElement(1, A), DomainElement(2, A), DomainElement(3, A), DomainElement(4, A)))
        )

        val transformer = new SymmetryBreakingTransformer(FunctionsFirstAnyOrder)

        transformer(typechecker(ProblemState(theory, scopes))) should be (ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true, haveRunNNF=false, verbose = false)))
    }

    test("with symmetry breaking") {
        val theory = Theory.empty
          .withSorts(A, B)
          .withConstantDeclarations(c1 of A, c2 of A, d1 of B)
          .withFunctionDeclaration(g)
          .withAxiom(Forall(x of A, x === c2))

          // Inferred types should be c1 of X1, c2 of X2, d1 of X3, g from X4 to X5

        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))

        val expected = theory
          .withAxiom(c1 === DomainElement(1, A))
          .withAxiom(c2 === DomainElement(1, A))
          .withAxiom(d1 === DomainElement(1, B))
          .withAxiom(App("g", DomainElement(1, A)) === DomainElement(1, A))
          .withAxiom( (App("g", DomainElement(2, A)) === DomainElement(1, A)) or (App("g", DomainElement(2, A)) === DomainElement(2, A) ) )
          .withAxiom((App("g", DomainElement(2, A)) === DomainElement(2, A) ) ==> (App("g", DomainElement(1, A)) === DomainElement(1, A)))

        val expectedRangeFormulas = Set(
          RangeRestriction(c1, Seq(DomainElement(1, A))),
          RangeRestriction(c2, Seq(DomainElement(1, A))),
          RangeRestriction(d1, Seq(DomainElement(1, B))),
          RangeRestriction(App("g", DomainElement(1, A)), Seq(DomainElement(1, A))),
          RangeRestriction(App("g", DomainElement(2, A)), Seq(DomainElement(1, A), DomainElement(2, A)))
        )

        val transformer = new SymmetryBreakingTransformer(SymmetryBreakingOptions(FunctionsFirstAnyOrder, breakSkolem = true, sortInference = true, patternOptimization = false))
        transformer(typechecker(ProblemState(theory, scopes))) should be (ProblemState(expected, scopes, Set.empty, Set.empty, expectedRangeFormulas, List.empty, Flags(distinctConstants = true)))
    }
}
