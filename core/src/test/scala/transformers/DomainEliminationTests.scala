import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class DomainEliminationTests extends UnitSuite {
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
                
        val _1A = DomainElement(1, A).asSmtConstant
        val _2A = DomainElement(2, A).asSmtConstant
        val _1B = DomainElement(1, B).asSmtConstant
        val _2B = DomainElement(2, B).asSmtConstant
        val _3B = DomainElement(3, B).asSmtConstant
        val _4B = DomainElement(4, B).asSmtConstant
        
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
        
        val transformer = DomainEliminationTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
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
        
        val _1A = DomainElement(1, A).asSmtConstant
        val _1B = DomainElement(1, B).asSmtConstant
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withConstants(c of A, d of B)
            .withConstants(_1A of A, _1B of B)
            .withAxiom(c === _1A)
            .withAxiom(d === _1B)
        
        val transformer = DomainEliminationTransformer
        transformer(ProblemState(theory, scopes)) should be (ProblemState(expectedTheory, scopes))
    }
}
