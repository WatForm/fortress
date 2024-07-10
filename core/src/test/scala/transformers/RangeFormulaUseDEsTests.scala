import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class RangeFormulaUseDEsTests extends UnitSuite {
    
    val transformer = RangeFormulaUseDEsTransformer

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
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, c2 of A, d1 of B)
            .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
            .withAxiom(Or(c2 === DomainElement(1, A), c2 === DomainElement(2, A)))
            .withAxiom(Or(d1 === DomainElement(1, B), d1 === DomainElement(2, B)))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(2))
        val transformer = RangeFormulaUseDEsTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("function arity 1") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
            .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
            .withAxiom(Or(d1 === DomainElement(1, B), d1 === DomainElement(2, B), d1 === DomainElement(3, B)))
            .withAxiom(Or(
                App("f", DomainElement(1, A)) === DomainElement(1, B),
                App("f", DomainElement(1, A)) === DomainElement(2, B),
                App("f", DomainElement(1, A)) === DomainElement(3, B)))
            .withAxiom(Or(
                App("f", DomainElement(2, A)) === DomainElement(1, B),
                App("f", DomainElement(2, A)) === DomainElement(2, B),
                App("f", DomainElement(2, A)) === DomainElement(3, B)))
            .withAxiom(Or(
                App("g", DomainElement(1, B)) === DomainElement(1, A),
                App("g", DomainElement(1, B)) === DomainElement(2, A)))
            .withAxiom(Or(
                App("g", DomainElement(2, B)) === DomainElement(1, A),
                App("g", DomainElement(2, B)) === DomainElement(2, A)))
            .withAxiom(Or(
                App("g", DomainElement(3, B)) === DomainElement(1, A),
                App("g", DomainElement(3, B)) === DomainElement(2, A)))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("function arity 2") {
        val theory = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
        
        val expected = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
            .withAxiom(Or(
                App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(1, C),
                App("f", DomainElement(1, A), DomainElement(1, B)) === DomainElement(2, C)))
            .withAxiom(Or(
                App("f", DomainElement(2, A), DomainElement(1, B)) === DomainElement(1, C),
                App("f", DomainElement(2, A), DomainElement(1, B)) === DomainElement(2, C)))
            .withAxiom(Or(
                App("f", DomainElement(1, A), DomainElement(2, B)) === DomainElement(1, C),
                App("f", DomainElement(1, A), DomainElement(2, B)) === DomainElement(2, C)))
            .withAxiom(Or(
                App("f", DomainElement(2, A), DomainElement(2, B)) === DomainElement(1, C),
                App("f", DomainElement(2, A), DomainElement(2, B)) === DomainElement(2, C)))
            .withAxiom(Or(
                App("f", DomainElement(1, A), DomainElement(3, B)) === DomainElement(1, C),
                App("f", DomainElement(1, A), DomainElement(3, B)) === DomainElement(2, C)))
            .withAxiom(Or(
                App("f", DomainElement(2, A), DomainElement(3, B)) === DomainElement(1, C),
                App("f", DomainElement(2, A), DomainElement(3, B)) === DomainElement(2, C)))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3), C -> ExactScope(2))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    // TODO replace this with property check?
    test("function arity 3") {
        val theory = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, A, C))
        
        val argumentTuples: Seq[Tuple3[Term, Term, Term]] = 
            for(i <- 1 to 5; j <- 1 to 7; k <- 1 to 5)
            yield (DomainElement(i, A), DomainElement(j, B), DomainElement(k, A))
        
        val rangeFormulas = argumentTuples.map { case (arg1, arg2, arg3) =>
            Or(App("f", arg1, arg2, arg3) === DomainElement(1, C),
               App("f", arg1, arg2, arg3) === DomainElement(2, C)) }
        
        val expected = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, A, C))
            .withAxioms(rangeFormulas)
        
        val scopes = Map(A -> ExactScope(5), B -> ExactScope(7), C -> ExactScope(2))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("boolean constants/predicates not restricted") {
        val theory = Theory.empty
            .withSort(A)
            .withConstantDeclaration(c1 of A)
            .withConstantDeclarations(p of Sort.Bool, q of Sort.Bool)
            .withFunctionDeclaration(FuncDecl("P", A, Sort.Bool))
            .withAxiom(p === q)
            .withAxiom(App("P", c1))
        
        val expected = theory
            .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
            // Nothing about p, q, P
        
        val scopes = Map(A -> ExactScope(2))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, c2 of A, c3 of A, d1 of B, d2 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
        
        val expected = theory
            .withAxiom(c1 === DomainElement(1, A))
            .withAxiom(c2 === DomainElement(1, A))
            .withAxiom(c3 === DomainElement(1, A))
            .withAxiom(d1 === DomainElement(1, B))
            .withAxiom(d2 === DomainElement(1, B))
            .withAxiom(App("f", DomainElement(1, A)) === DomainElement(1, B))
            .withAxiom(App("g", DomainElement(1, B)) === DomainElement(1, A))
        
        val scopes = Map(A -> ExactScope(1), B -> ExactScope(1))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("builtin types universally quantified") {
         val theory = Theory.empty
            .withSort(A)
            .withConstantDeclarations(c1 of IntSort, c2 of A, c3 of BoolSort)
            .withFunctionDeclaration(FuncDecl("f", BoolSort, A, IntSort, A))
            .withFunctionDeclaration(FuncDecl("g", IntSort, A, BoolSort, A))
         
         val x0 = Var("$x_0")
         val x1 = Var("$x_1")
         
         val expected = theory
            .withAxiom((c2 === DomainElement(1, A)) or (c2 === DomainElement(2, A)))
            .withAxiom(Forall(Seq(x0 of BoolSort, x1 of IntSort), Or(
                App("f", x0, DomainElement(1, A), x1) === DomainElement(1, A),
                App("f", x0, DomainElement(1, A), x1) === DomainElement(2, A))))
            .withAxiom(Forall(Seq(x0 of BoolSort, x1 of IntSort), Or(
                App("f", x0, DomainElement(2, A), x1) === DomainElement(1, A),
                App("f", x0, DomainElement(2, A), x1) === DomainElement(2, A))))
            .withAxiom(Forall(Seq(x0 of IntSort, x1 of BoolSort), Or(
                App("g", x0, DomainElement(1, A), x1) === DomainElement(1, A),
                App("g", x0, DomainElement(1, A), x1) === DomainElement(2, A))))
            .withAxiom(Forall(Seq(x0 of IntSort, x1 of BoolSort), Or(
                App("g", x0, DomainElement(2, A), x1) === DomainElement(1, A),
                App("g", x0, DomainElement(2, A), x1) === DomainElement(2, A))))
        
        val scopes = Map(A -> ExactScope(2))
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expected, scopes))
    }
    
    test("existing range restriction: if term already restricted, don't generate range formulas") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
        
        val rangeRestrictions = Set(
            RangeRestriction(c1, Seq(DomainElement(2, A))),
            RangeRestriction(App("f", DomainElement(1, A)), Seq(DomainElement(3, B), DomainElement(1, B))),
            RangeRestriction(App("g", DomainElement(3, B)), Seq(DomainElement(1, A))),
            RangeRestriction(App("g", DomainElement(1, B)), Seq(DomainElement(1, A)))
        )
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
            // .withAxiom(Or(c1 === DomainElement(1, A), c1 === DomainElement(2, A)))
            .withAxiom(Or(d1 === DomainElement(1, B), d1 === DomainElement(2, B), d1 === DomainElement(3, B)))
            // .withAxiom(Or(
            //     App("f", DomainElement(1, A)) === DomainElement(1, B),
            //     App("f", DomainElement(1, A)) === DomainElement(2, B),
            //     App("f", DomainElement(1, A)) === DomainElement(3, B)))
            .withAxiom(Or(
                App("f", DomainElement(2, A)) === DomainElement(1, B),
                App("f", DomainElement(2, A)) === DomainElement(2, B),
                App("f", DomainElement(2, A)) === DomainElement(3, B)))
            // .withAxiom(Or(
            //     App("g", DomainElement(1, B)) === DomainElement(1, A),
            //     App("g", DomainElement(1, B)) === DomainElement(2, A)))
            .withAxiom(Or(
                App("g", DomainElement(2, B)) === DomainElement(1, A),
                App("g", DomainElement(2, B)) === DomainElement(2, A)))
            // .withAxiom(Or(
            //     App("g", DomainElement(3, B)) === DomainElement(1, A),
            //     App("g", DomainElement(3, B)) === DomainElement(2, A)))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))
        val transformer = RangeFormulaUseDEsTransformer
        val problemState = ProblemState(
            theory,
            scopes,
            Set.empty,
            Set.empty,
            rangeRestrictions,
            List.empty,
            Flags(
                distinctConstants = true,
                haveRunNNF = false,
                verbose = false,
            ),
        )
        val expectedProblemState = ProblemState(
            expected,
            scopes,
            Set.empty,
            Set.empty,
            rangeRestrictions,
            List.empty,
            Flags(
                distinctConstants = true,
                haveRunNNF = false,
                verbose = false,
            ),
        )
        transformer(problemState) should be (expectedProblemState)
    }
}
