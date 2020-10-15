import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class SkolemizeTransformerTest extends UnitSuite with CommonFunctionalSymbols {
    
    val skolemizer = new SkolemizeTransformer
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val p = Var("p")
    val q = Var("q")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val _a = Var("a")
    val _b = Var("b")

    val R_1 = FunctionSymbol("R_1")
    val sk_0 = FunctionSymbol("sk_0")
    val sk_1 = FunctionSymbol("sk_1")
    val sk_2 = FunctionSymbol("sk_2")
    val sk_3 = FunctionSymbol("sk_3")
    val sk_4 = FunctionSymbol("sk_4")
    val sk_5 = FunctionSymbol("sk_5")
    val sk_6 = FunctionSymbol("sk_6")
    
    test("simple skolem constant") {
        val sk_0 = Var("sk_0")

        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withAxiom(Exists(y of A, P(y)))

        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withConstant(sk_0 of A)
            .withAxiom(P(sk_0))
            
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(sk_0 of A))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    test("simple skolem function") {
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withAxiom(Forall(x of A, Exists(y of A, Q(x, y))))
        
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(Forall(x of A, Q(x, sk_0(x))))
            
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A))
    }
    
    test("all exists all") {
        // z should not be part of the skolem function
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withAxiom(Forall(x of A, Exists(y of A, Forall(z of A, R(x, y, z)))))
        
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(Forall(x of A, Forall(z of A, R(x, sk_0(x), z))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A))
    }
    
    test("multiple skolem functions") {
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withAxiom(And(
                Forall(x of A, Exists(y of A, Q(x, y))),
                Forall(z of A, Exists(y of A, Q(y, z))),
                Exists(y of A, P(y))))
        
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withConstant(Var("sk_2") of A)
            .withAxiom(And(
                Forall(x of A, Q(x, sk_0(x))),
                Forall(z of A, Q(sk_1(z), z)),
                P(Var("sk_2"))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_2") of A))
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A, sk_1 from A to A))
    }
    
    // TODO how to test when technically the order of arguments is not guaranteed?
    // Will just have to do either or
    
    // Only the free variables actually used should be made as arguments to the skolem function
    test("only used vars 1") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(S from B to BoolSort)
            .withAxiom(Forall(x of A, Exists(y.of(B), S(y))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(S from B to BoolSort)
            .withConstant(Var("sk_0").of(B))
            .withAxiom(Forall(x of A, S(Var("sk_0"))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_0") of B))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    // Only the free variables actually used should be made as arguments to the skolem function
    test("only used vars 2") {
        val theory = Theory.empty
        .withSort(A)
        .withSort(B)
        .withFunctionDeclaration(T from (A, B) to BoolSort)
            .withAxiom(Forall(Seq(x of A, z of A), Exists(y.of(B), T(z, y))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(T from (A, B) to BoolSort)
            .withFunctionDeclaration(FuncDecl("sk_0", A, B))
            .withAxiom(Forall(Seq(x of A, z of A), T(z, sk_0(z))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, B)))
    }
    
    test("multivariable Exists") {
        val theory = Theory.empty
        .withSort(A)
        .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withAxiom(Forall(x of A, Exists(Seq(y of A, z of A), R(x, y, z))))
        
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withAxiom(Forall(x of A, R(x, sk_0(x), sk_1(x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A, sk_1 from A to A))
    }
    
    test("multi argument") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R_1 from (A, A, B) to BoolSort)
            .withAxiom(Forall(Seq(x of A, z.of(B)), Exists(y of A, R_1(x, y, z))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R_1 from (A, A, B) to BoolSort)
            .withFunctionDeclaration(FuncDecl("sk_0", A, B, A))
            .withAxiom(Forall(Seq(x of A, z.of(B)), R_1(x, sk_0(x, z), z)))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, B, A)))
    }
    
    // Constants should not be included as arguments to skolem functions
    test("not include constants") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R_1 from (A, A, B) to BoolSort)
            .withConstant(z.of(B))
            .withAxiom(Forall(x of A, Exists(y of A, R_1(x, y, z))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R_1 from (A, A, B) to BoolSort)
            .withConstant(z.of(B))
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(Forall(x of A, R_1(x, sk_0(x), z)))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A))
    }
    
    // Former bug: was not adding sk_0 to constants, so when encountering it
    // later after substituting the skolemizer thought it was a free variable,
    // and then could not find its type
    test("exists forall exists") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withAxiom(Exists(y of A, Forall(x of A, Exists(z of A, R(x, y, z)))))
        
        // Note that we skolemize out to in, which reduces nested applications
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, A) to BoolSort)
            .withConstant(Var("sk_0") of A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withAxiom(Forall(x of A, R(x, Var("sk_0"), sk_1(x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_0") of A))
        newProblemState.skolemFunctions should be (Set(sk_1 from A to A))
    }
    
    test("name generation 1") {
        // The names sk_0 is used
        // The next name should be sk_1
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withSort(Sort.mkSortConst("sk_0"))
            .withAxiom(Exists(y of A, P(y)))
                
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withSort(Sort.mkSortConst("sk_0"))
            .withConstant(Var("sk_1") of A)
            .withAxiom(P(Var("sk_1")))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_1") of A))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    test("name generation 2") {
        // The names sk_0, sk_1, sk_2, sk_4, sk_5 are used
        // The next names should be sk_3 and sk_6
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withSort(Sort.mkSortConst("sk_0"))
            .withFunctionDeclaration(FuncDecl("sk_1", A, Sort.Bool))
            .withConstant(Var("sk_2") of A)
            .withAxiom(Forall(Var("sk_4") of A, Top))
            .withAxiom(Forall(Var("sk_5") of A, Top))
            .withAxiom(And(
                Exists(y of A, P(y)),
                Forall(x of A, Exists(y of A, Q(x, y)))))
                
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withSort(Sort.mkSortConst("sk_0"))
            .withFunctionDeclaration(FuncDecl("sk_1", A, Sort.Bool))
            .withConstant(Var("sk_2") of A)
            .withAxiom(Forall(Var("sk_4") of A, Top))
            .withAxiom(Forall(Var("sk_5") of A, Top))
            .withConstant(Var("sk_3") of A)
            .withFunctionDeclaration(FuncDecl("sk_6", A, A))
            .withAxiom(And(
                P(Var("sk_3")),
                Forall(x of A, Q(x, App("sk_6", x)))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_3") of A))
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_6", A, A)))
    }
    
    test("multiple formulas") {
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withAxiom(Exists(y of A, P(y)))
            .withAxiom(Forall(x of A, Exists(y of A, Q(x, y))))
        
        // Either of the following is acceptable
        val expected1 = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withConstant(Var("sk_0") of A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withAxiom(P(Var("sk_0")))
            .withAxiom(Forall(x of A, Q(x, sk_1(x))))
        
        val expected2 = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withConstant(Var("sk_1") of A)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(P(Var("sk_1")))
            .withAxiom(Forall(x of A, Q(x, sk_0(x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should (equal (expected1) or equal (expected2))
        newProblemState.skolemConstants should (
            equal (Set(Var("sk_0") of A))
            or equal (Set(Var("sk_1") of A)))
        newProblemState.skolemFunctions should (
            equal (Set(sk_1 from A to A))
            or equal (Set(sk_0 from A to A)))
    }

    test("shadow variable (old fortress bug)") {

        val P = FunctionSymbol("P")
        val Q = FunctionSymbol("Q")
        val sk_0 = FunctionSymbol("sk_0")

        val theory1 = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withAxiom(Forall(Seq(_a of A, _b of B), Exists(_b of B,
                {P(_a) and Q(_a, _b)}
                or
                {!P(_a) and !Q(_a, _b)}
            )))
            // ∀a,b | ∃b | (p[a] && q[a,b]) || (!p[a] && !q[a,b])

        val theory2 = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to B)
            .withAxiom(Forall(Seq(_a of A, _b of B),
                {P(_a) and Q(_a, sk_0(_a))}
                or
                {!P(_a) and !Q(_a, sk_0(_a))}
            ))
        
        val newProblemState = skolemizer(ProblemState(theory1))
        newProblemState.theory should be (theory2)
    }
}
