import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate._

class SkolemizeTransformerTest extends UnitSuite with CommonSymbols {
    
    def skolemizer(th:Theory) = 
        SkolemizeTransformer(
            NnfTransformer(
                IfLiftingTransformer(
                    TypecheckSanitizeTransformer(ProblemState(th)))))    

    val _a = Var("a")
    val _b = Var("b")

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
            .withConstantDeclaration(sk_0 of A)
            .withAxiom(P(sk_0))
        
        skolemizer(theory).theory should be (expected)
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
            
        skolemizer(theory).theory should be (expected)
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
        
        skolemizer(theory).theory should be (expected)
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
            .withConstantDeclaration(Var("sk_2") of A)
            .withAxiom(And(
                Forall(x of A, Q(x, sk_0(x))),
                Forall(z of A, Q(sk_1(z), z)),
                P(Var("sk_2"))))
        
        skolemizer(theory).theory should be (expected)
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
            .withConstantDeclaration(Var("sk_0").of(B))
            .withAxiom(Forall(x of A, S(Var("sk_0"))))
        
        skolemizer(theory).theory should be (expected)
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
            .withFunctionDeclaration(sk_0 from A to B)
            .withAxiom(Forall(Seq(x of A, z of A), T(z, sk_0(z))))
        
        skolemizer(theory).theory should be (expected)
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
        
        skolemizer(theory).theory should be (expected)
    }
    
    test("multi argument") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, B) to BoolSort)
            .withAxiom(Forall(Seq(x of A, z of B), Exists(y of A, R(x, y, z))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, B) to BoolSort)
            .withFunctionDeclaration(sk_0 from (A, B) to A)
            .withAxiom(Forall(Seq(x of A, z of B), R(x, sk_0(x, z), z)))
        
        skolemizer(theory).theory should be (expected)
    }
    
    // Constants should not be included as arguments to skolem functions
    test("not include constants") {
        val theory = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, B) to BoolSort)
            .withConstantDeclaration(z of B)
            .withAxiom(Forall(x of A, Exists(y of A, R(x, y, z))))
        
        val expected = Theory.empty
            .withSort(A)
            .withSort(B)
            .withFunctionDeclaration(R from (A, A, B) to BoolSort)
            .withConstantDeclaration(z of B)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(Forall(x of A, R(x, sk_0(x), z)))
        
        skolemizer(theory).theory should be (expected)
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
            .withConstantDeclaration(Var("sk_0") of A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withAxiom(Forall(x of A, R(x, Var("sk_0"), sk_1(x))))
        
        skolemizer(theory).theory should be (expected)
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
            .withConstantDeclaration(Var("sk_1") of A)
            .withAxiom(P(Var("sk_1")))
        
        skolemizer(theory).theory should be (expected)
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
            .withFunctionDeclaration(sk_1 from A to BoolSort)
            .withConstantDeclaration(Var("sk_2") of A)
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
            .withFunctionDeclaration(sk_1 from A to BoolSort)
            .withConstantDeclaration(Var("sk_2") of A)
            .withAxiom(Forall(Var("sk_4") of A, Top))
            .withAxiom(Forall(Var("sk_5") of A, Top))
            .withConstantDeclaration(Var("sk_3") of A)
            .withFunctionDeclaration(sk_6 from A to A)
            .withAxiom(And(
                P(Var("sk_3")),
                Forall(x of A, Q(x, sk_6(x)))))
        
        skolemizer(theory).theory should be (expected)
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
            .withConstantDeclaration(Var("sk_0") of A)
            .withFunctionDeclaration(sk_1 from A to A)
            .withAxiom(P(Var("sk_0")))
            .withAxiom(Forall(x of A, Q(x, sk_1(x))))
        
        val expected2 = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withConstantDeclaration(Var("sk_1") of A)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(P(Var("sk_1")))
            .withAxiom(Forall(x of A, Q(x, sk_0(x))))
        
        skolemizer(theory).theory should (equal (expected1) or equal(expected2))
    }

    test("exists shadowing forall variable (old fortress bug)") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withAxiom(Forall(Seq(_a of A, _b of B), Exists(_b of B,
                {P(_a) and Q(_a, _b)}
                or
                {!P(_a) and !Q(_a, _b)}
            )))
            // ∀a,b | ∃b | (p[a] && q[a,b]) || (!p[a] && !q[a,b])

        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withFunctionDeclaration(sk_0 from A to B)
            .withAxiom(Forall(Seq(_a of A, _b of B),
                {P(_a) and Q(_a, sk_0(_a))}
                or
                {!P(_a) and !Q(_a, sk_0(_a))}
            ))
        
        skolemizer(theory).theory should be (expected)
    }

    test("skolem functions, constants added to problem state") {
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
            .withConstantDeclaration(Var("sk_2") of A)
            .withAxiom(And(
                Forall(x of A, Q(x, sk_0(x))),
                Forall(z of A, Q(sk_1(z), z)),
                P(Var("sk_2"))))
        
        val newProblemState = SkolemizeTransformer(ProblemState(theory))
        newProblemState.theory should be (expected)
        newProblemState.skolemConstants should be (Set(Var("sk_2") of A))
        newProblemState.skolemFunctions should be (Set(sk_0 from A to A, sk_1 from A to A))
    }

    test("forall variable shadowing signature constant (former bug)") {
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withConstantDeclaration(x of A)
            .withAxiom(Forall(x of A, Exists(y of A, Q(x, y))))

        /* This used to be a bug - when deciding if the ocurrence of x in Q(x, y) is a free variable
        *  that needs to be an argument to the skolem function, the skolemizer would just look at the
        *  free variables of Q(x, y) and subtract away the constants of the signature.
        *  However this fails to notice that x was quantified by an earlier forall.
        */
        
        val expected = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(Q from (A, A) to BoolSort)
            .withConstantDeclaration(x of A)
            .withFunctionDeclaration(sk_0 from A to A)
            .withAxiom(Forall(x of A, Q(x, sk_0(x))))
        
        skolemizer(theory).theory should be (expected)
    }

    test("forall variable shadowing another forall variable") {
        val theory = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(Q from (C, A) to BoolSort)
            .withFunctionDeclaration(P from B to BoolSort)
            .withAxiom(Forall(x of B, P(x) and Forall(x of C, Exists(y of A, Q(x, y)))))
        
        val expected = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(Q from (C, A) to BoolSort)
            .withFunctionDeclaration(P from B to BoolSort)
            .withFunctionDeclaration(sk_0 from C to A)
            .withAxiom(Forall(x of B, P(x) and Forall(x of C, Q(x, sk_0(x)))))
        
        skolemizer(theory).theory should be (expected)
    }

    test("No change inside a ITE conditional"){
        val theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(y of A, z of A)
            .withFunctionDeclaration(P from (A,A) to BoolSort)
            .withAxiom(IfThenElse(Forall(x1.of(A), Exists(x2 of A, P(x1, x2))), Eq(y,z), Not(Eq(y,z))))

        val expected = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(y of A, z of A)
            .withFunctionDeclaration(P from (A, A) to BoolSort)
            .withAxiom(IfThenElse(Forall(x1.of(A), Exists(x2 of A, P(x1, x2))), Eq(y,z), Not(Eq(y,z))))

            skolemizer(theory).theory should be (expected)
    }

    test("Function Definition"){
        val fDef = FunctionDefinition(
            "Q",
            Seq(x of A),
            BoolSort,
            Exists(z of A, App(P.name, x, z))
        )

        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclaration(P from (A, A) to BoolSort)
            .withFunctionDefinition(fDef)
            .withConstantDeclaration(y of A)
            .withAxiom(App("Q", y))

        val expectedFDef = FunctionDefinition(
            "Q",
            Seq(x of A),
            BoolSort,
            App(P.name, x, sk_0(x))
        )

        val expected = Theory.empty
            .withSorts(A)
            .withFunctionDeclaration(P from (A, A) to BoolSort)
            .withFunctionDeclaration(sk_0 from (A) to A)
            .withConstantDeclaration(y of A)
            .withAxiom(App("Q", y))
            .withFunctionDefinition(expectedFDef)
        
        skolemizer(theory).theory should be (expected)

    }

    test("Constant Definition"){
        val xDef = ConstantDefinition(x of BoolSort,
            Exists(Seq(y of A), Eq(y, z))
        )

        val theory = Theory.empty
            .withSort(A)
            .withConstantDeclaration(z of A)
            .withConstantDefinition(xDef)

        val result = skolemizer(theory).theory

        result.constantDefinitions.toSeq(0) should be (ConstantDefinition(AnnotatedVar(x, BoolSort), Eq(Var("sk_0"), z)))
        // We can and probably should do more complicated tests

    }
}
