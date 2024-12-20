import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.problemstate._

class SetCardinalityTransformerTests extends UnitSuite {
    val cardinality = SetCardinalityTransformer

    def prep(x:Theory) =
        TypecheckSanitizeTransformer(ProblemState(x))

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val P1 = FuncDecl("p1", A, Sort.Bool)
    val P2 = FuncDecl("p2", B, Sort.Bool)
    val F = FuncDecl("f", A, B)
    val G = FuncDecl("g", Seq(A,A), B)
    
    val a1 = Var("a1")
    val a2 = Var("a2")
    val a3 = Var("a3")
    val a4 = Var("a4")
    val b = Var("b")

    val c1 = App("p1", a1)
    val c2 = App("p1", a2)

    val fa1 = App("f", a1)
    val fa2 = App("f", a2)
    val fa3 = App("f", a3)
    
    def expectedFunctions(p: String, sort: Sort, scope: Int, cardNum: Int): Seq[FunctionDefinition] ={
        val inP_args: Seq[AnnotatedVar] = Seq(AnnotatedVar(Var("x_" + cardNum), sort))
        val inP_body = IfThenElse(App(p, Seq(Var("x_" + cardNum))), IntegerLiteral(1), IntegerLiteral(0))
        val inP = FunctionDefinition("inP_" + cardNum, inP_args, IntSort, inP_body)
        
        val cardP_args: Seq[Term] = for (num <- 1 to scope) yield App("inP_" + cardNum, DomainElement(num, sort))
        var cardP_body : Term = IntegerLiteral(0)
        for (arg <- cardP_args) {
            cardP_body = Term.mkPlus(cardP_body, arg)
        }
        val cardP = FunctionDefinition("cardP_" + cardNum, Seq(), IntSort, cardP_body)
        
        return Seq(inP, cardP)
    }
    
    
    val baseTheory = Theory.empty
        .withSorts(A,B)
        .withConstantDeclarations(a1 of A, a2 of A, a3 of A, a4 of A, b of B)
        .withFunctionDeclarations(P1, P2, F, G)
        
    test("no effect") {
        val theory = baseTheory
            .withAxiom(Eq(fa1,fa2))
        val expected = baseTheory
            .withAxiom(Eq(fa1,fa2)) 
        cardinality(prep(theory))
            .theory should be(expected)                  
    }
    
    test("simple cardinality") {
        val theory = baseTheory
            .withAxiom(Eq(SetCardinality("p1"),IntegerLiteral(4)))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4)))
        
        val expected = baseTheory
            .withAxiom(Eq(Var("cardP_0"),IntegerLiteral(4)))
            .withFunctionDefinitions(expectedFunctions("p1", A, 4, 0)) 

        cardinality(ps)
            .theory should be(expected)
    }

    test("double cardinality") {     
        val theory = baseTheory
            .withAxiom(Eq(SetCardinality("p1"),IntegerLiteral(3)))
            .withAxiom(Eq(SetCardinality("p2"),IntegerLiteral(5)))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Eq(Var("cardP_0"),IntegerLiteral(3)))
            .withAxiom(Eq(Var("cardP_1"),IntegerLiteral(5)))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)
    }

    test("equal cardinality") {      
        val theory = baseTheory
            .withAxiom(Eq(SetCardinality("p1"),SetCardinality("p2")))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Eq(Var("cardP_0"), Var("cardP_1")))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)          
    }

    test("not equal cardinality") {
        val theory = baseTheory
            .withAxiom(Not(Eq(SetCardinality("p1"),SetCardinality("p2"))))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Not(Eq(Var("cardP_0"), Var("cardP_1"))))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)    
    }

    test("addition cardinality") {    
        val theory = baseTheory
            .withAxiom(Eq(Term.mkPlus(SetCardinality("p1"),SetCardinality("p2")), SetCardinality("p1")))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Eq(Term.mkPlus(Var("cardP_0"), Var("cardP_1")), Var("cardP_0")))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)                
    }
    
    test("subtraction cardinality") {   
        val theory = baseTheory
            .withAxiom(Eq(Term.mkSub(SetCardinality("p1"),SetCardinality("p2")), SetCardinality("p1")))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Eq(Term.mkSub(Var("cardP_0"), Var("cardP_1")), Var("cardP_0")))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)             
    }
    
    test("implies cardinality"){
        val theory = baseTheory
            .withAxiom(Implication(Eq(SetCardinality("p1"), IntegerLiteral(2)), Eq(SetCardinality("p2"), IntegerLiteral(4))))
            .withAxiom(Iff(Eq(SetCardinality("p1"), IntegerLiteral(5)), Eq(SetCardinality("p2"), IntegerLiteral(5))))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4), B -> ExactScope(9)))
        
        val funcList = expectedFunctions("p1", A, 4, 0) ++ expectedFunctions("p2", B, 9, 1)

        val expected = baseTheory
            .withAxiom(Implication(Eq(Var("cardP_0"), IntegerLiteral(2)), Eq(Var("cardP_1"), IntegerLiteral(4))))
            .withAxiom(Iff(Eq(Var("cardP_0"), IntegerLiteral(5)), Eq(Var("cardP_1"), IntegerLiteral(5))))
            .withFunctionDefinitions(funcList(0)) // matching axiom declaration order
            .withFunctionDefinitions(funcList(2))
            .withFunctionDefinitions(funcList(3)) 
            .withFunctionDefinitions(funcList(1))
        
        cardinality(ps)
            .theory should be(expected)   
    }
}