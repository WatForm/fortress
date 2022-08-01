import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class QuantifierExpansionTests extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val b = Var("b")
    val P = FuncDecl("P", A, Sort.Bool)
    val Q = FuncDecl("Q", B, Sort.Bool)
    val R = FuncDecl("R", A, B, Sort.Bool)
    val f = FuncDecl("f", A, B)
    val g = FuncDecl("g", A, A)
    
    test("single variable forall") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(x of A, App("P", x)))
            .withAxiom(Forall(y of B, App("Q", y)))
       
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))
            
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(And(
                App("P", DomainElement(1, A)),
                App("P", DomainElement(2, A))))
            .withAxiom(And(
                App("Q", DomainElement(1, B)),
                App("Q", DomainElement(2, B)),
                App("Q", DomainElement(3, B))))
        
        val expectedScopes = scopes
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, expectedScopes))
    }
    
    test("multivariable forall") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(Seq(x of A, y of A, z of B),
                (App("P", x) and App("P", y)) ==> App("Q", z) ))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(3))
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(And(
                (App("P", DomainElement(1, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(1, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(1, B)),
                (App("P", DomainElement(1, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(1, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(1, B)),
                (App("P", DomainElement(1, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(2, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(2, B)),
                (App("P", DomainElement(1, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(2, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(2, B)),
                (App("P", DomainElement(1, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(3, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(1, A))) ==> App("Q", DomainElement(3, B)),
                (App("P", DomainElement(1, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(3, B)),
                (App("P", DomainElement(2, A)) and App("P", DomainElement(2, A))) ==> App("Q", DomainElement(3, B))))
        
        val expectedScopes = scopes
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, expectedScopes))
    }
    
    test("nested foralls") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q, R, g)
            .withAxiom(Forall(x of A, (App("g", x) === x) or (Forall(y of B, App("R", x, y)))))
            
            
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(2))
        
        val t1A = (App("g", DomainElement(1, A)) === DomainElement(1, A)) or 
            (App("R", DomainElement(1, A), DomainElement(1, B)) and (App("R", DomainElement(1, A), DomainElement(2, B))))
        
        val t2A = (App("g", DomainElement(2, A)) === DomainElement(2, A)) or 
            (App("R", DomainElement(2, A), DomainElement(1, B)) and (App("R", DomainElement(2, A), DomainElement(2, B))))
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q, R, g)
            .withAxiom(t1A and t2A)
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
    }
    
    test("constants not expanded") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            .withConstant(b of B)
            .withAxiom(Forall(x of A, App("f", x) === b))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(2))
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            .withConstant(b of B)
            .withAxiom(And(
                App("f", DomainElement(1, A)) === b,
                App("f", DomainElement(2, A)) === b))
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(x of A, App("P", x)))
            .withAxiom(Forall(y of B, App("Q", y)))
        
        val scopes = Map(A -> ExactScope(1), B -> ExactScope(1))
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(App("P", DomainElement(1, A)))
            .withAxiom(App("Q", DomainElement(1, B)))
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
    }
    
    test("Builtin types not expanded") {
        val A = SortConst("A")
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(FuncDecl("P", A, IntSort, BoolSort, BoolSort))
            .withAxiom(Forall( Seq(x of A, y of IntSort, z of BoolSort), App("P", x, y, z)))
            
        val scopes: Map[Sort, Scope] = Map(A -> ExactScope(2))
        
        val expectedTheory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(FuncDecl("P", A, IntSort, BoolSort, BoolSort))
            .withAxiom(Forall( Seq(y of IntSort, z of BoolSort),
                App("P", DomainElement(1, A), y, z) and App("P", DomainElement(2, A), y, z)))
        
        val transformer = StandardQuantifierExpansionTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
    }
    
    test("Existential quantifiers expanded") {
        pending
    }
}
