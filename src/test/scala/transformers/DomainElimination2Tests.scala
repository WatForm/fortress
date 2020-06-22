import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class DomainElimination2Tests extends UnitSuite {
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val c = Var("c")
    val d = Var("d")
    val x = Var("x")
    
    test("standard domain elimination") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstants(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withAxiom(App("f", c, DomainElement(1, A)) === DomainElement(3, B))
            .withAxiom(Not(d === DomainElement(4, B)) ==> Exists(x of A, x === DomainElement(2, A)))
        
        val scopes = Map(A -> 2, B -> 4)
                
        val _1A = Var("$1A")
        val _2A = Var("$2A")
        val _1B = Var("$1B")
        val _2B = Var("$2B")
        val _3B = Var("$3B")
        val _4B = Var("$4B")
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withConstants(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withConstants(
                _1A of A,
                _2A of A,
                _1B of B,
                _2B of B,
                _3B of B,
                _4B of B)
            .withAxiom(Distinct(_1A, _2A))
            .withAxiom(Distinct(_1B, _2B, _3B, _4B))
            .withAxiom(App("f", c, _1A) === _3B)
            .withAxiom(Not(d === _4B) ==> Exists(x of A, x === _2A))
        
        val transformer = new DomainEliminationTransformer2
        transformer(Problem(theory, scopes)) should be (Problem(expectedTheory, scopes))
    }
    
    test("out of bounds scope error") {
        pending
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstants(c of A, d of B)
            .withAxiom(c === DomainElement(1, A))
            .withAxiom(d === DomainElement(1, B))
        
        val scopes = Map(A -> 1, B -> 1)
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withConstants(c of A, d of B)
            .withConstants(Var("$1A") of A, Var("$1B") of B)
            .withAxiom(c === Var("$1A"))
            .withAxiom(d === Var("$1B"))
        
        val transformer = new DomainEliminationTransformer2
        transformer(Problem(theory, scopes)) should be (Problem(expectedTheory, scopes))
    }
}
