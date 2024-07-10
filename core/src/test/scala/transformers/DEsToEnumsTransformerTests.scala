import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class DEstoEnumsTransformerTests extends UnitSuite {
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val c = Var("c")
    val d = Var("d")
    val x = Var("x")
    
    test("standard domain elimination") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withAxiom(App("f", c, DomainElement(1, A)) === DomainElement(3, B))
            .withAxiom(Not(d === DomainElement(4, B)) ==> Exists(x of A, x === DomainElement(2, A)))
        
        val scopes = Map(A -> ExactScope(2), B -> ExactScope(4))

        val _1A = DomainElement(1, A).asEnumValue
        val _2A = DomainElement(2, A).asEnumValue
        val _1B = DomainElement(1, B).asEnumValue
        val _2B = DomainElement(2, B).asEnumValue
        val _3B = DomainElement(3, B).asEnumValue
        val _4B = DomainElement(4, B).asEnumValue
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c of A, d of B)
            .withFunctionDeclaration(FuncDecl("f", A, A, B))
            .withEnumSort(A, _1A, _2A)
            .withEnumSort(B, _1B, _2B, _3B, _4B)
            .withAxiom(App("f", c, _1A) === _3B)
            .withAxiom(Not(d === _4B) ==> Exists(x of A, x === _2A))
        
        val transformer = DEsToEnumsTransformer
        transformer(ProblemState(theory, scopes)) should be(ProblemState(
            expectedTheory,
            scopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty,
            Flags(
                distinctConstants = false,
                verbose = false,
                haveRunNNF = false
            ),
        ))
    }
    
    test("scope of one") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c of A, d of B)
            .withAxiom(c === DomainElement(1, A))
            .withAxiom(d === DomainElement(1, B))
        
        val scopes = Map(A -> ExactScope(1), B -> ExactScope(1))
        
        val _1A = DomainElement(1, A).asEnumValue
        val _1B = DomainElement(1, B).asEnumValue
        
        val expectedTheory = Theory.empty
            .withSorts(A, B)
            .withConstantDeclarations(c of A, d of B)
            .withEnumSort(A, _1A)
            .withEnumSort(B, _1B)
            .withAxiom(c === _1A)
            .withAxiom(d === _1B)
        
        val transformer = DEsToEnumsTransformer
        transformer(ProblemState(theory, scopes)) should be(ProblemState(
            expectedTheory,
            scopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty,
            Flags(
            distinctConstants = false,
            verbose = false,
            haveRunNNF = false,
            ),
        ))
    }
}
