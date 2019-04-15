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
        pending
        // val theory = Theory.empty
        //     .withTypes(A, B)
        //     .withConstants(c of A, d of B)
        //     .withFunctionDeclaration(FuncDecl("f", A, A, B))
        //     .withAxiom(App("f", c, DomainElement(1, A)) === DomainElement(3, B))
        //     .withAxiom(Not(d === DomainElement(4, B)) ==> Exists(x of A, x === DomainElement(2, A)))
        // 
        // val _1A = DomainElement(1, A).asSmtConstant
        // val _3B = DomainElement(3, B).asSmtConstant
        // val _4B = DomainElement(4, B).asSmtConstant
        // val _2A = DomainElement(2, A).asSmtConstant
        // 
        // val expected = Theory.empty
        //     .withTypes(A, B)
        //     .withConstants(c of A, d of B)
        //     .withFunctionDeclaration(FuncDecl("f", A, A, B))
        //     // .withConstants()
        //     // .withAxiom(distinct)
        // 
        //     .withAxiom(App("f", c, _1A) === _3B)
        //     .withAxiom(Not(d === _4B) ==> Exists(x of A, x === _2A))
        // 
        // scopes
        // val transformer = new DomainEliminationTransformer()
        // transformer(theory) should be (expected)
    }
    
    test("out of bounds scope error") {
        pending
    }
}
