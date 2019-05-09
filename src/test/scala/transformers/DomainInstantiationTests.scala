import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner


import fortress.msfol._
import fortress.transformers._
import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class DomainInstantiationTests extends FunSuite with Matchers {
    
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
            
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(And(
                App("P", DomainElement(1, A)),
                App("P", DomainElement(2, A))))
            .withAxiom(And(
                App("Q", DomainElement(1, B)),
                App("Q", DomainElement(2, B)),
                App("Q", DomainElement(3, B))))
        
        val scopes = Map(A -> 2, B -> 3)
        val transformer = new DomainInstantiationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("multivariable forall") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(Seq(x of A, y of A, z of B),
                (App("P", x) and App("P", y)) ==> App("Q", z) ))
        
        val expected = Theory.empty
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
        
        val scopes = Map(A -> 2, B -> 3)
        val transformer = new DomainInstantiationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("nested foralls") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q, R, g)
            .withAxiom(Forall(x of A, (App("g", x) === x) or (Forall(y of B, App("R", x, y)))))
        
        val t1A = (App("g", DomainElement(1, A)) === DomainElement(1, A)) or 
            (App("R", DomainElement(1, A), DomainElement(1, B)) and (App("R", DomainElement(1, A), DomainElement(2, B))))
        
        val t2A = (App("g", DomainElement(2, A)) === DomainElement(2, A)) or 
            (App("R", DomainElement(2, A), DomainElement(1, B)) and (App("R", DomainElement(2, A), DomainElement(2, B))))
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q, R, g)
            .withAxiom(t1A and t2A)
        
        val scopes = Map(A -> 2, B -> 2)
        val transformer = new DomainInstantiationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("constants not expanded") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            .withConstant(b of B)
            .withAxiom(Forall(x of A, App("f", x) === b))
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            .withConstant(b of B)
            .withAxiom(And(
                App("f", DomainElement(1, A)) === b,
                App("f", DomainElement(2, A)) === b))
        
        val scopes = Map(A -> 2, B -> 2)
        val transformer = new DomainInstantiationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(x of A, App("P", x)))
            .withAxiom(Forall(y of B, App("Q", y)))
        
        val expected = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(App("P", DomainElement(1, A)))
            .withAxiom(App("Q", DomainElement(1, B)))
        
        val scopes = Map(A -> 1, B -> 1)
        val transformer = new DomainInstantiationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("unspecified type ???") {
        pending
    }
    
    test("expanding a nonexistent type fails") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(x of A, App("P", x)))
            .withAxiom(Forall(y of B, App("Q", y)))
        
        val scopes = Map(A -> 2, B -> 2, C -> 2)
        val transformer = new DomainInstantiationTransformer(scopes)
        
        a [fortress.util.Errors.PreconditionException] should be thrownBy (transformer(theory))
    }
    
    test("boolean scope fails") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
            .withAxiom(Forall(x of A, App("P", x)))
            .withAxiom(Forall(y of B, App("Q", y)))
        
        val scopes = Map(A -> 2, B -> 2, Sort.Bool -> 3)
        val transformer = new DomainInstantiationTransformer(scopes)
        
        a [fortress.util.Errors.PreconditionException] should be thrownBy (transformer(theory))
    }
}
