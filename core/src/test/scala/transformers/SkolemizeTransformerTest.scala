import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class SkolemizeTransformerTest extends UnitSuite {
    
    val skolemizer = new SkolemizeTransformer
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val p = Var("p")
    val q = Var("q")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    
    val f = FuncDecl.mkFuncDecl("f", A, A)
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)
    val Q = FuncDecl.mkFuncDecl("Q", A, A, Sort.Bool)
    val R = FuncDecl.mkFuncDecl("R", A, A, A, Sort.Bool)
    val S = FuncDecl.mkFuncDecl("S", B, Sort.Bool)
    val T = FuncDecl.mkFuncDecl("T", A, B, Sort.Bool)
    val R_1 = FuncDecl.mkFuncDecl("R_1", A, A, B, Sort.Bool)
    
    val baseTheory = Theory.empty
        .withSort(A)
        .withSort(B)
        .withConstant(p.of(Sort.Bool))
        .withConstant(q.of(Sort.Bool))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
        .withFunctionDeclaration(Q)
        .withFunctionDeclaration(R)
        .withFunctionDeclaration(S)
        .withFunctionDeclaration(T)
        .withFunctionDeclaration(R_1)
    
    test("simple skolem constant") {
        val theory = baseTheory
            .withAxiom(Exists(y.of(A), App("P", y)))

        val expected = baseTheory
            .withConstant(Var("sk_0").of(A))
            .withAxiom(App("P", Var("sk_0")))
            
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_0") of A))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    test("simple skolem function") {
        val theory = baseTheory
            .withAxiom(Forall(x.of(A), Exists(y.of(A), App("Q", x, y))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Forall(x.of(A), App("Q", x, App("sk_0", x))))
            
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, A)))
    }
    
    test("all exists all") {
        // z should not be part of the skolem function
        val theory = baseTheory
            .withAxiom(Forall(x.of(A), Exists(y.of(A), Forall(z.of(A), App("R", x, y, z)))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Forall(x.of(A), Forall(z.of(A), App("R", x, App("sk_0", x), z))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, A)))
    }
    
    test("multiple skolem functions") {
        val theory = baseTheory
            .withAxiom(And(
                Forall(x.of(A), Exists(y.of(A), App("Q", x, y))),
                Forall(z.of(A), Exists(y.of(A), App("Q", y, z))),
                Exists(y.of(A), App("P", y))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withConstant(Var("sk_2").of(A))
            .withAxiom(And(
                Forall(x.of(A), App("Q", x, App("sk_0", x))),
                Forall(z.of(A), App("Q", App("sk_1", z), z)),
                App("P", Var("sk_2"))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_2") of A))
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, A), FuncDecl("sk_1", A, A)))
    }
    
    // TODO how to test when technically the order of arguments is not guaranteed?
    // Will just have to do either or
    
    // Only the free variables actually used should be made as arguments to the skolem function
    test("only used vars 1") {
        val theory = baseTheory
            .withAxiom(Forall(x.of(A), Exists(y.of(B), App("S", y))))
        
        val expected = baseTheory
            .withConstant(Var("sk_0").of(B))
            .withAxiom(Forall(x.of(A), App("S", Var("sk_0"))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_0") of B))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    // Only the free variables actually used should be made as arguments to the skolem function
    test("only used vars 2") {
        val theory = baseTheory
            .withAxiom(Forall(Seq(x.of(A), z.of(A)), Exists(y.of(B), App("T", z, y))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, B))
            .withAxiom(Forall(Seq(x.of(A), z.of(A)), App("T", z, App("sk_0", z))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, B)))
    }
    
    test("multivariable Exists") {
        val theory = baseTheory
            .withAxiom(Forall(x.of(A), Exists(Seq(y.of(A), z.of(A)), App("R", x, y, z))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(Forall(x.of(A), App("R", x, App("sk_0", x), App("sk_1", x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, A), FuncDecl("sk_1", A, A)))
    }
    
    test("multi argument") {
        val theory = baseTheory
            .withAxiom(Forall(Seq(x.of(A), z.of(B)), Exists(y.of(A), App("R_1", x, y, z))))
        
        val expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, B, A))
            .withAxiom(Forall(Seq(x.of(A), z.of(B)), App("R_1", x, App("sk_0", x, z), z)))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, B, A)))
    }
    
    // Constants should not be included as arguments to skolem functions
    test("not include constants") {
        val theory = baseTheory
            .withConstant(z.of(B))
            .withAxiom(Forall(x.of(A), Exists(y.of(A), App("R_1", x, y, z))))
        
        val expected = baseTheory
            .withConstant(z.of(B))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Forall(x.of(A), App("R_1", x, App("sk_0", x), z)))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set.empty[AnnotatedVar])
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_0", A, A)))
    }
    
    // Former bug: was not adding sk_0 to constants, so when encountering it
    // later after substituting the skolemizer thought it was a free variable,
    // and then could not find its type
    test("exists forall exists") {
        val theory = baseTheory
            .withAxiom(Exists(y.of(A), Forall(x.of(A), Exists(z.of(A), App("R", x, y, z)))))
        
        // Note that we skolemize out to in, which reduces nested applications
        val expected = baseTheory
            .withConstant(Var("sk_0").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(Forall(x.of(A), App("R", x, Var("sk_0"), App("sk_1", x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_0") of A))
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_1", A, A)))
    }
    
    test("name generation 1") {
        // The names sk_0 is used
        // The next name should be sk_1
        val theory = baseTheory
            .withSort(Sort.mkSortConst("sk_0"))
            .withAxiom(Exists(y.of(A), App("P", y)))
                
        val expected = baseTheory
            .withSort(Sort.mkSortConst("sk_0"))
            .withConstant(Var("sk_1").of(A))
            .withAxiom(App("P", Var("sk_1")))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_1") of A))
        newProblemState.skolemFunctions should be (Set.empty[FuncDecl])
    }
    
    test("name generation 2") {
        // The names sk_0, sk_1, sk_2, sk_4, sk_5 are used
        // The next names should be sk_3 and sk_6
        val theory = baseTheory
            .withSort(Sort.mkSortConst("sk_0"))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, Sort.Bool))
            .withConstant(Var("sk_2").of(A))
            .withAxiom(Forall(Var("sk_4").of(A), Top))
            .withAxiom(Forall(Var("sk_5").of(A), Top))
            .withAxiom(And(
                Exists(y.of(A), App("P", y)),
                Forall(x.of(A), Exists(y.of(A), App("Q", x, y)))))
                
        val expected = baseTheory
            .withSort(Sort.mkSortConst("sk_0"))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, Sort.Bool))
            .withConstant(Var("sk_2").of(A))
            .withAxiom(Forall(Var("sk_4").of(A), Top))
            .withAxiom(Forall(Var("sk_5").of(A), Top))
            .withConstant(Var("sk_3").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_6", A, A))
            .withAxiom(And(
                App("P", Var("sk_3")),
                Forall(x.of(A), App("Q", x, App("sk_6", x)))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_3") of A))
        newProblemState.skolemFunctions should be (Set(FuncDecl("sk_6", A, A)))
    }
    
    test("multiple formulas") {
        val theory = baseTheory
            .withAxiom(Exists(y.of(A), App("P", y)))
            .withAxiom(Forall(x.of(A), Exists(y.of(A), App("Q", x, y))))
        
        // Either of the following is acceptable
        val expected1 = baseTheory
            .withConstant(Var("sk_0").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(App("P", Var("sk_0")))
            .withAxiom(Forall(x.of(A), App("Q", x, App("sk_1", x))))
        
        val expected2 = baseTheory
            .withConstant(Var("sk_1").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(App("P", Var("sk_1")))
            .withAxiom(Forall(x.of(A), App("Q", x, App("sk_0", x))))
        
        val newProblemState = skolemizer(ProblemState(theory))
        newProblemState.theory should (equal (expected1) or equal (expected2))
        newProblemState.skolemConstants should (
            equal (Set(Var("sk_0") of A))
            or equal (Set(Var("sk_1") of A)))
        newProblemState.skolemFunctions should (
            equal (Set(FuncDecl("sk_1", A, A)))
            or equal (Set(FuncDecl("sk_0", A, A))))
    }
}
