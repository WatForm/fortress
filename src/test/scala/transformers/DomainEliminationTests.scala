import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.tfol._
import fortress.transformers._

@RunWith(classOf[JUnitRunner])
class DomainEliminationTests extends FunSuite with Matchers {
    val A = Type.mkTypeConst("A")
    val B = Type.mkTypeConst("B")
    
    val c = Var("c")
    val d = Var("d")
    val x = Var("x")
    
    test("standard domain elimination") {
        val theory = Theory.empty
            .withTypes(A, B)
            .withConstants(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withAxiom(App("f", c, DomainElement(1, A)) === DomainElement(3, B))
            .withAxiom(Not(d === DomainElement(4, B)) ==> Exists(x of A, x === DomainElement(2, A)))
        
        val _1A = Var("@1A")
        val _3B = Var("@3B")
        val _4B = Var("@4B")
        val _2A = Var("@2A")
        
        val expected = Theory.empty
            .withTypes(A, B)
            .withConstants(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withConstants(
                Var("@1A") of A,
                Var("@2A") of A,
                Var("@3A") of A,
                Var("@1B") of B,
                Var("@2B") of B,
                Var("@3B") of B,
                Var("@4B") of B)
            .withAxiom(Distinct(Var("@1A"), Var("@2A"), Var("@3A")))
            .withAxiom(Distinct(Var("@1B"), Var("@2B"), Var("@3B"), Var("@4B")))
            .withAxiom(App("f", c, _1A) === _3B)
            .withAxiom(Not(d === _4B) ==> Exists(x of A, x === _2A))
        
        val scopes = Map(A -> 3, B -> 4)
        val transformer = new DomainEliminationTransformer(scopes)
        transformer(theory) should be (expected)
    }
    
    test("out of bounds scope error") {
        pending
    }
}