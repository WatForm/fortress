import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.tfol._
import fortress.transformers._

@RunWith(classOf[JUnitRunner])
class RangeFormulaTests extends FunSuite with Matchers {
    
    val A = Type.mkTypeConst("A")
    val B = Type.mkTypeConst("B")
    val C = Type.mkTypeConst("C")
    
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
            .withTypes(A, B)
            .withConstants(c1 of A, c2 of A, d1 of B)
        
        val expected = Theory.empty
            .withTypes(A, B)
            .withConstants(c1 of A, c2 of A, d1 of B)
            .withAxiom(c1 === DomainElement(1, A))
            .withAxiom(Or(c2 === DomainElement(1, A), c2 === DomainElement(2, A)))
            .withAxiom(d1 === DomainElement(1, B))
        
        val scopes = Map(A -> 2, B -> 2)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("function arity 1") {
        val theory = Theory.empty
            .withTypes(A, B)
            .withConstants(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
        
        val expected = Theory.empty
            .withTypes(A, B)
            .withConstants(c1 of A, d1 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
            .withFunctionDeclaration(FuncDecl("g", B, A))
            .withAxiom(c1 === DomainElement(1, A))
            .withAxiom(d1 === DomainElement(1, B))
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
        
        val scopes = Map(A -> 2, B -> 3)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("function arity 2") {
        val theory = Theory.empty
            .withTypes(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
        
        val expected = Theory.empty
            .withTypes(A, B, C)
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
        
        val scopes = Map(A -> 2, B -> 3, C -> 2)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    // TODO replace this with property check?
    test("function arity 3") {
        val theory = Theory.empty
            .withTypes(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, A, C))
        
        val argumentTuples: Seq[Tuple3[Term, Term, Term]] = 
            for(i <- 1 to 5; j <- 1 to 7; k <- 1 to 5)
            yield (DomainElement(i, A), DomainElement(j, B), DomainElement(k, A))
        
        val rangeFormulas = argumentTuples.map { case (arg1, arg2, arg3) =>
            Or(App("f", arg1, arg2, arg3) === DomainElement(1, C),
               App("f", arg1, arg2, arg3) === DomainElement(2, C)) }
        
        val expected = Theory.empty
            .withTypes(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, A, C))
            .withAxioms(rangeFormulas)
        
        val scopes = Map(A -> 5, B -> 7, C -> 2)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("more constants than scope (symmetry)") {
        val theory = Theory.empty
            .withType(A)
            .withConstants(c1 of A, c2 of A, c3 of A, c4 of A)
            .withFunctionDeclaration(FuncDecl("f", A, A))
            
        val expected = theory
            .withAxiom(c1 === DomainElement(1, A))
            .withAxiom( (c2 === DomainElement(1, A)) or (c2 === DomainElement(2, A)) )
            .withAxiom( (c3 === DomainElement(1, A)) or (c3 === DomainElement(2, A)) )
            .withAxiom( (c4 === DomainElement(1, A)) or (c4 === DomainElement(2, A)) )
            .withAxiom( (App("f", DomainElement(1, A)) === DomainElement(1, A))
                or (App("f", DomainElement(1, A)) === DomainElement(2, A)) )
            .withAxiom( (App("f", DomainElement(2, A)) === DomainElement(1, A))
                or (App("f", DomainElement(2, A)) === DomainElement(2, A)) )
        
        val scopes = Map(A -> 2)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("boolean constants/predicates not restricted") {
        val theory = Theory.empty
            .withType(A)
            .withConstant(c1 of A)
            .withConstants(p of Type.Bool, q of Type.Bool)
            .withFunctionDeclaration(FuncDecl("P", A, Type.Bool))
            .withAxiom(p === q)
            .withAxiom(App("P", c1))
        
        val expected = theory
            .withAxiom(c1 === DomainElement(1, A))
            // Nothing about p, q, P
        
        val scopes = Map(A -> 2)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("boolean scope fails") {
        val theory = Theory.empty
            .withType(A)
            .withConstant(c1 of A)
            .withConstants(p of Type.Bool, q of Type.Bool)
            .withFunctionDeclaration(FuncDecl("P", A, Type.Bool))
            .withAxiom(p === q)
            .withAxiom(App("P", c1))
        
        val scopes = Map(A -> 2, Type.Bool -> 3)
        val transformer = new RangeFormulaTransformer(scopes)
        a [fortress.util.Errors.PreconditionException] should be thrownBy (transformer(theory))
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withTypes(A, B)
            .withConstants(c1 of A, c2 of A, c3 of A, d1 of B, d2 of B)
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
        
        val scopes = Map(A -> 1, B -> 1)
        val transformer = new RangeFormulaTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("non existant type errors") {
        val theory = Theory.empty
            .withType(A)
            .withConstant(c1 of A)
        
        val scopes = Map(A -> 2, B -> 1)
        val transformer = new RangeFormulaTransformer(scopes)
        a [fortress.util.Errors.PreconditionException] should be thrownBy (transformer(theory))
    }
    
    test("unspecified types ???") {
        // What to do if unspecified scope?
        pending
    }
}
