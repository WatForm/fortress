import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate.ProblemState

class IfLiftingTransformerTest extends UnitSuite {

	val iflift = IfLiftingTransformer
    val typechecker = TypecheckSanitizeTransformer

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val P = FuncDecl("p", A, Sort.Bool)
    val F = FuncDecl("f", A, B)
    val G = FuncDecl("g", Seq(A,A), B)


    val a1 = Var("a1")
    val a2 = Var("a2")
    val a3 = Var("a3")
    val a4 = Var("a4")
    val b = Var("b")

    val c1 = App("p", a1)
    val c2 = App("p", a2)

    val fa1 = App("f", a1)
    val fa2 = App("f", a2)
    val fa3 = App("f", a3)

    val KDefn = FunctionDefinition("K", Seq((Var("x")) of A), B, 
            App("f", IfThenElse(c1,Var("x"),a2)))
    val KDefnLifted = FunctionDefinition("K", Seq((Var("x")) of A), B, 
            IfThenElse(c1, App("f", Var("x")), App("f", a2)))
    

    val baseTheory = Theory.empty
        .withSorts(A,B)
        .withConstantDeclarations(a1 of A, a2 of A, a3 of A, a4 of A, b of B)
        .withFunctionDeclarations(P, F, G)

    test("no effect") {
        val theory = baseTheory
            .withAxiom(Eq(fa1,fa2))
        val expected = baseTheory
            .withAxiom(Eq(fa1,fa2)) 
        iflift(typechecker(ProblemState(theory))).theory should be(expected)                  
    }
    test("simple ite") {
    	val theory = baseTheory
    		.withAxiom(Eq( App("f", IfThenElse(c1,a1,a2)),b))
    	val expected = baseTheory
    		.withAxiom(OrList(
    					AndList(c1, Eq(fa1,b)),
    					AndList(Not(c1), Eq(fa2,b))
    				   ))
    	iflift(typechecker(ProblemState(theory))).theory should be(expected)
    }

    test("nested ite") {
        val theory = baseTheory
            .withAxiom(Eq(
                App("f", IfThenElse(c1,IfThenElse(c2,a1,a2),a3)),
                b))
        val expected = baseTheory
            .withAxiom(OrList(
                AndList(
                    c1,
                    OrList(
                        AndList(c2, Eq(fa1,b)),
                        AndList(Not(c2), Eq(fa2,b))
                    )),
                AndList(Not(c1), Eq(fa3,b))
            ))
        iflift(typechecker(ProblemState(theory))).theory should be(expected)
    }

    test("other arg ite") {
        val theory = baseTheory
            .withAxiom(Eq(
                App("g", a1, IfThenElse(c1,a2,a3)),
                b))
        val expected = baseTheory
            .withAxiom(OrList(
                AndList(
                    c1,
                    Eq(App("g",a1,a2),b)),
                AndList(Not(c1), Eq(App("g",a1,a3),b))
            ))
        iflift(typechecker(ProblemState(theory))).theory should be(expected)        
    }

    test("ite in multiple args") {
        val theory = baseTheory
            .withAxiom(Eq(
                b,
                App("g", IfThenElse(c1,a1,a2), IfThenElse(c2,a3,a4))
            ))
        val expected = baseTheory
            .withAxiom(OrList
                (AndList(
                    c1,
                    OrList(
                        AndList(c2, Eq(b,App("g",a1,a3))),
                        AndList(Not(c2), Eq(b,App("g",a1,a4)))
                    )),
                AndList(
                    Not(c1),
                    OrList(
                        AndList(c2, Eq(b,App("g",a2,a3))),
                        AndList(Not(c2), Eq(b,App("g",a2,a4)))
                    ))
                ))  
        iflift(typechecker(ProblemState(theory))).theory should be(expected)             
    }

    test("ite in both sides of Eq") {
        val theory = baseTheory
            .withAxiom(Eq(
                App("f",IfThenElse(c1,a1,a2)),
                App("f",IfThenElse(c2,a3,a4))
            ))
        val expected = baseTheory
            .withAxiom(
                OrList(
                    AndList(
                        c1,
                        OrList(
                            AndList(c2,Eq(App("f",a1),App("f",a3))),
                            AndList(Not(c2),Eq(App("f",a1),App("f",a4)))
                        )),
                   AndList(
                        Not(c1),
                        OrList(
                            AndList(c2,Eq(App("f",a2),App("f",a3))),
                            AndList(Not(c2),Eq(App("f",a2),App("f",a4)))
                        ))
                )
            )
        iflift(typechecker(ProblemState(theory))).theory should be(expected)         
    }

    test("and/not list") {
        val theory = baseTheory
            .withAxiom(
                AndList(
                    Eq(
                        App("f",IfThenElse(c1,a1,a2)),
                        App("f",IfThenElse(c2,a3,a4))
                    ),
                    Not(Eq(fa1,fa2))
                )
            )
        val expected = baseTheory
            .withAxiom(
                AndList(
                    OrList(
                        AndList(
                            c1,
                            OrList(
                                AndList(c2,Eq(App("f",a1),App("f",a3))),
                                AndList(Not(c2),Eq(App("f",a1),App("f",a4)))
                            )),
                       AndList(
                            Not(c1),
                            OrList(
                                AndList(c2,Eq(App("f",a2),App("f",a3))),
                                AndList(Not(c2),Eq(App("f",a2),App("f",a4)))
                            ))
                    ),
                    Not(Eq(fa1,fa2))
                )
            )
        iflift(typechecker(ProblemState(theory))).theory should be(expected)         
    } 

    test("imp") {
        val theory = baseTheory
            .withAxiom(
                Implication(
                    Eq(
                        App("f",IfThenElse(c1,a1,a2)),
                        App("f",IfThenElse(c2,a3,a4))
                    ),
                    Not(Eq(fa1,fa2))
                )
            )
        val expected = baseTheory
            .withAxiom(
                Implication(
                    OrList(
                        AndList(
                            c1,
                            OrList(
                                AndList(c2,Eq(App("f",a1),App("f",a3))),
                                AndList(Not(c2),Eq(App("f",a1),App("f",a4)))
                            )),
                       AndList(
                            Not(c1),
                            OrList(
                                AndList(c2,Eq(App("f",a2),App("f",a3))),
                                AndList(Not(c2),Eq(App("f",a2),App("f",a4)))
                            ))
                    ),
                    Not(Eq(fa1,fa2))
                ))
        iflift(typechecker(ProblemState(theory))).theory should be(expected)         
    }   

    test("non-Boolean ite") {
        val theory = baseTheory
            .withFunctionDefinition(KDefn)
        val expected = baseTheory
            .withFunctionDefinition(KDefnLifted)

        iflift(typechecker(ProblemState(theory))).theory should be(expected)       

    }     
}