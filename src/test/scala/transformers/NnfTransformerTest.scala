import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.transformers._

@RunWith(classOf[JUnitRunner])
class NnfTransformerTest extends FunSuite with Matchers {
    
    val nnf = new NnfTransformer
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val p = Var("p")
    val q = Var("q")
    val x = Var("x")
    val y = Var("y")
    
    val f = FuncDecl.mkFuncDecl("f", A, A)
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)
    
    val baseTheory = Theory.empty
        .withSort(A)
        .withSort(B)
        .withConstant(p.of(Sort.Bool))
        .withConstant(q.of(Sort.Bool))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
    
    test("simple And Theory") {
        val theory = baseTheory
            .withAxiom(Not(And(p, Not(p))))
        
        val expected = baseTheory
            .withAxiom(Or(Not(p), p))
        
        nnf(theory) should be (expected)
    }
    
    test("nnf Imp") {
        val theory = baseTheory
            .withAxiom(Implication(p, q))
            
        val expected = baseTheory
            .withAxiom(Or(Not(p), q))

        nnf(theory) should be (expected)
    }

    test("nnf Iff") {
        val theory = baseTheory
            .withAxiom(Eq(p, q))
            
        val expected = baseTheory
            .withAxiom(Or(And(p, q),
                                 And(Not(p), Not(q))))

        nnf(theory) should be (expected)
    }

    test("nnf Not And") {
        val theory = baseTheory
            .withAxiom(Not(And(p, q)))
            
        val expected = baseTheory
            .withAxiom(Or(Not(p), Not(q)))

        nnf(theory) should be (expected)
    }
    
    test("nnfNotOr") {
        val theory = baseTheory
            .withAxiom(Not(Or(p, q)))
            
        val expected = baseTheory
            .withAxiom(And(Not(p), Not(q)))

        nnf(theory) should be (expected)
    }

    test("nnf Not Not") {
        val theory = baseTheory
            .withAxiom(Not(Not(p)))
            
        val expected = baseTheory
            .withAxiom(p)

        nnf(theory) should be (expected)
    }

    test("nnf Not Exists") {
        val theory = baseTheory
            .withAxiom(Not(Exists(x.of(A), App("P", x))))
            
        val expected = baseTheory
            .withAxiom(Forall(x.of(A), Not(App("P", x))))

        nnf(theory) should be (expected)
    }

    test("nnf Not Forall") {
        val theory = baseTheory
            .withAxiom(Not(Forall(x.of(A), App("P", x))))
            
        val expected = baseTheory
            .withAxiom(Exists(x.of(A), Not(App("P", x))))

        nnf(theory) should be (expected)
    }
    
    test("nnf Not Imp") {
        val theory = baseTheory
            .withAxiom(Not(Implication(p, q)))
            
        val expected = baseTheory
            .withAxiom(And(p, Not(q)))

        nnf(theory) should be (expected)
    }

    test("nnf Not Iff") {
        val theory = baseTheory
            .withAxiom(Not(Eq(p, q)))
            
        val expected = baseTheory
            .withAxiom(Or(And(p, Not(q)),
                                 And(Not(p), q)))

        nnf(theory) should be (expected)
    }
    
    test("complex1") {
        val axiom = Not(
            Exists(
                x.of(A),
                Eq(
                    Not(p),
                    Not(Or(q, p)))))
        val expectedAxiom =
            Forall(
                x.of(A),
                Or(
                    And(Not(p), Or(q, p)),
                    And(p, And(Not(q), Not(p)))))
        val theory = baseTheory.withAxiom(axiom)
        val expected = baseTheory.withAxiom(expectedAxiom)
        nnf(theory) should be (expected)
    }
    
    test("complex2") {
        // ~ ( exists x . (~p) <=> ~(q OR (forall x . ~(P(x) AND (~~q) => p))) )
        val axiom = Not(
            Exists(
                x.of(A),
                Eq(
                    Not(p),
                    Not(
                        Or(
                            q,
                            Forall(
                                x.of(A),
                                Not(
                                    And(
                                        App("P", x),
                                        Implication(
                                            Not(Not(q)),
                                            p
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
        // forall x. (~p AND (q OR (forall x . ~P(x) OR (q AND ~p))))
        //        OR (p AND (~q AND exists x . P(x) AND (~q OR p)))
        val expectedAxiom =
            Forall(
                x.of(A),
                Or(
                    And(
                        Not(p),
                        Or(
                            q,
                            Forall(
                                x.of(A),
                                Or(
                                    Not(App("P", x)),
                                    And(
                                        q,
                                        Not(p)
                                    )
                                )
                            )
                        )
                    ),
                    And(
                        p,
                        And(
                            Not(q),
                            Exists(
                                x.of(A),
                                And(
                                    App("P", x),
                                    Or(
                                        Not(q),
                                        p
                                    )
                                )
                            )
                        )
                    )
                )
            )
        val theory = baseTheory
            .withAxiom(axiom)
            
        val expected = baseTheory
            .withAxiom(expectedAxiom)
        
        nnf(theory) should be (expected)
    }
    
    test("distinct - former bug") { // Former bug
        val U = Sort.mkSortConst("U")
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        val P = FuncDecl.mkFuncDecl("P", U, U, U, Sort.Bool)
        
        val t = Forall(Seq(x.of(U), y.of(U), z.of(U)),
            Implication(App("P", x, y, z), Distinct(x, y, z)))
        
        val e = Forall(Seq(x.of(U), y.of(U), z.of(U)),
            Or(
                Not(App("P", x, y, z)),
                And(
                    Not(Eq(x, y)),
                    Not(Eq(x, z)),
                    Not(Eq(y, z)))))
                    
        val base = Theory.empty
            .withSort(U)
            .withFunctionDeclaration(P)
        val theory = base.withAxiom(t)
        val expected = base.withAxiom(e)
        
        nnf(theory) should be (expected)
    }
    
    test("distinct2 - former bug") { // Former bug
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
            Implication(
                And(
                    Not(Eq(x1, x2)),
                    Not(Eq(x1, x3)),
                    Not(Eq(x2, x3))),
                Not(Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
        
        val base = Theory.empty
            .withSort(V)
            .withFunctionDeclaration(adj)
        
        val theory1 = base.withAxiom(t1)
        val theory2 = base.withAxiom(t2)
        
        nnf(theory1) should be (nnf(theory2))
    }
    
    test("distinct3") {
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
            Implication(
                And(
                    Not(Eq(x1, x2)),
                    Not(Eq(x1, x3)),
                    Not(Eq(x2, x3))),
                Not(Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
        
        val base = Theory.empty
            .withSort(V)
            .withFunctionDeclaration(adj)
        
        val theory1 = base.withAxiom(t1)
        val theory2 = base.withAxiom(t2)
        
        nnf(theory1) should be (nnf(theory2))
    }
}
