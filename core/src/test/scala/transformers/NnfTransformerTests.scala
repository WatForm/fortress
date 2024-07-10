import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate._

class NnfTransformerTests extends UnitSuite with CommonSymbols {

    val nnf = NnfTransformer

    def checkTransform(input: Theory, expected: Theory) = {
        val ps = ProblemState(input).withFlags(Flags(haveRunIfLifting = true))
        nnf(ps).theory should equal (expected)
    }

    val _a = Var("a")
    val _b = Var("b")


    
    val baseTheory = Theory.empty
        .withSort(A)
        .withSort(B)
        .withConstantDeclaration(p of BoolSort)
        .withConstantDeclaration(q of BoolSort)
        .withFunctionDeclaration(P from A to BoolSort)
    
    test("and") {
        val theory = baseTheory
            .withAxiom(Not(And(p, Not(p))))
        
        val expected = baseTheory
            .withAxiom(Or(Not(p), p))
        
        checkTransform(theory, expected)
    }

    test("and in constant defs") {
        val theory = baseTheory
            .withConstantDefinition(ConstantDefinition(
                _a of BoolSort,
                Not(And(p, Not(p)))
            ))
        val expected = baseTheory
            .withConstantDefinition(ConstantDefinition(
                _a of BoolSort,
                Or(Not(p), p)
            ))
        checkTransform(theory, expected)
    }

    test("and in function defs"){
        val theory = baseTheory
            .withFunctionDefinition(FunctionDefinition(
                "a", Seq(p of BoolSort), BoolSort,
                Not(And(p, Not(q)))
            ))
        val expected = baseTheory
            .withFunctionDefinition(FunctionDefinition(
                "a", Seq(p of BoolSort), BoolSort,
                Or(Not(p), q)
            ))
        checkTransform(theory, expected)
    }
    
    test("imp") {
        val theory = baseTheory
            .withAxiom(Implication(p, q))
            
        val expected = baseTheory
            .withAxiom(Or(Not(p), q))

        checkTransform(theory, expected)
    }

    test("iff") {
        val theory = baseTheory
            .withAxiom(Iff(p, q))
            
        val expected = baseTheory
            .withAxiom(Or(And(p, q), And(Not(p), Not(q))))

        checkTransform(theory, expected)
    }

    test("not and") {
        val theory = baseTheory
            .withAxiom(Not(And(p, q)))
            
        val expected = baseTheory
            .withAxiom(Or(Not(p), Not(q)))

        checkTransform(theory, expected)
    }
    
    test("not or") {
        val theory = baseTheory
            .withAxiom(Not(Or(p, q)))
            
        val expected = baseTheory
            .withAxiom(And(Not(p), Not(q)))

        checkTransform(theory, expected)
    }

    test("not not") {
        val theory = baseTheory
            .withAxiom(Not(Not(p)))
            
        val expected = baseTheory
            .withAxiom(p)

        checkTransform(theory, expected)
    }

    test("not exists") {
        val theory = baseTheory
            .withAxiom(Not(Exists(x.of(A), App("P", x))))
            
        val expected = baseTheory
            .withAxiom(Forall(x.of(A), Not(App("P", x))))

        checkTransform(theory, expected)
    }

    test("not forall") {
        val theory = baseTheory
            .withAxiom(Not(Forall(x.of(A), App("P", x))))
            
        val expected = baseTheory
            .withAxiom(Exists(x.of(A), Not(App("P", x))))

        checkTransform(theory, expected)
    }
    
    test("not imp") {
        val theory = baseTheory
            .withAxiom(Not(Implication(p, q)))
            
        val expected = baseTheory
            .withAxiom(And(p, Not(q)))

        checkTransform(theory, expected)
    }

    test("not iff") {
        val theory = baseTheory
            .withAxiom(Not(Iff(p, q)))
            
        val expected = baseTheory
            .withAxiom(Or(And(p, Not(q)), And(Not(p), q)))

        checkTransform(theory, expected)
    }
    
    test("complex 1") {
        val axiom = Not(
            Exists(x of A,
                Iff(
                    Not(p),
                    Not(Or(q, p)))))
        val expectedAxiom =
            Forall(x of A,
                Or(
                    And(Not(p), Or(q, p)),
                    And(p, And(Not(q), Not(p)))))
        val theory = baseTheory.withAxiom(axiom)
        val expected = baseTheory.withAxiom(expectedAxiom)
        checkTransform(theory, expected)
    }
    
    test("complex 2") {
        // ~ ( exists x . (~p) <=> ~(q OR (forall x . ~(P(x) AND (~~q) => p))) )
        val axiom = !Exists(x of A, !p <==> !(q or Forall(x of A, !(P(x) and (!(!q) ==> p)))))

        // forall x. (~p AND (q OR (forall x . ~P(x) OR (q AND ~p))))
        //        OR (p AND (~q AND exists x . P(x) AND (~q OR p)))
        val expectedAxiom =
            Forall(x of A,
                {!p and (q or Forall(x of A, !P(x) or (q and !p)))}
                or
                {p and (!q and Exists(x of A, P(x) and (!q or p)))})

        val theory = baseTheory
            .withAxiom(axiom)
            
        val expected = baseTheory
            .withAxiom(expectedAxiom)
        
        checkTransform(theory, expected)
    }
    
    test("distinct (former bug)") {
        val U = Sort.mkSortConst("U")
        
        val t = Forall(Seq(x of U, y of U, z of U), P(x, y, z) ==> Distinct(x, y, z))
        
        val e = Forall(Seq(x of U, y of U, z of U), !P(x, y, z) or And(!(x === y), !(x === z), !(y === z)))
                    
        val base = Theory.empty
            .withSort(U)
            .withFunctionDeclaration(P from (U, U, U) to BoolSort)
        val theory = base.withAxiom(t)
        val expected = base.withAxiom(e)
        
        checkTransform(theory, expected)
    }
    
    test("distinct 2 (former bug)") {
        val V = Sort.mkSortConst("V")
        val adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool)
        val x1 = Var("x1")
        val x2 = Var("x2")
        val x3 = Var("x3")
        
        val t1 = Forall(Seq(x1.of(V), x2.of(V), x3.of(V)),
            Implication(
                Distinct(x1, x2, x3),
                Not(Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
                    
        val t2 = Forall(Seq(x1.of(V), x2.of(V), x3.of(V)),
            Or(
                Or(
                    Eq(x1, x2),
                    Eq(x1, x3),
                    Eq(x2, x3))
                ,
                Not(Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
        
        val base = Theory.empty
            .withSort(V)
            .withFunctionDeclaration(adj)
        
        val theory1 = base.withAxiom(t1)
        val theory2 = base.withAxiom(t2)
       
        // 2024-07-10 NAD bug corrected here
        // can't just run nnf on result
        // we are testing nnf! 
        //val resultTheory2 = nnf(ProblemState(theory2)).theory
        checkTransform(theory1, theory2)
    }
    
    test("distinct 3") {
        val V = Sort.mkSortConst("V")
        val adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool)
        val x1 = Var("x1")
        val x2 = Var("x2")
        val x3 = Var("x3")
        
        val t1 = Not(Exists(Seq(x1.of(V), x2.of(V), x3.of(V)),
            And(
                Distinct(x1, x2, x3),
                (Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3))))))
                    
        val t2 = Forall(Seq(x1.of(V), x2.of(V), x3.of(V)),
            Or(
                Or(
                    Eq(x1, x2),
                    Eq(x1, x3),
                    Eq(x2, x3)),
                Not(Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
        
        val base = Theory.empty
            .withSort(V)
            .withFunctionDeclaration(adj)
        
        val theory1 = base.withAxiom(t1)
        val theory2 = base.withAxiom(t2)

        // 2024-07-10 NAD bug corrected here
        // can't just run nnf on result
        // we are testing nnf!         
        //val resultTheory2 = nnf(ProblemState(theory2)).theory
        checkTransform(theory1, theory2)
    }

    test("forall iff") {
        val theory1 = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withAxiom(Forall(_a of A, P(_a) <==> Forall(_b of B, Q(_a, _b))))
            // ∀a | p[a] <=> (∀b | q[a,b])
        
        val theory2 = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(P from A to BoolSort)
            .withFunctionDeclaration(Q from (A, B) to BoolSort)
            .withAxiom(Forall(_a of A,
                { P(_a) and Forall(_b of B, Q(_a, _b)) }
                or { !P(_a) and Exists(_b of B, !Q(_a, _b)) } ) )
            // ∀a | (p[a] && (∀b | q[a,b])) || (!p[a] && (∃b | !q[a,b]))
        
        checkTransform(theory1, theory2)
    }
}
