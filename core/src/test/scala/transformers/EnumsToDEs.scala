import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class EnumsToDEsTests extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    
    val x = Var("x")
    
    test("compute appropriate mapping") {
        val theory = Theory.empty
            .withEnumSort(A, EnumValue("cat"), EnumValue("dog"), EnumValue("mouse"))
            .withSort(B)
            .withEnumSort(C, EnumValue("red"), EnumValue("blue"))
        
        val mapping = EnumsToDEsTransformer.computeEnumSortMapping(theory)
        val expected = Map(
            EnumValue("cat") -> DomainElement(1, A),
            EnumValue("dog") -> DomainElement(2, A),
            EnumValue("mouse") -> DomainElement(3, A),
            EnumValue("red") -> DomainElement(1, C),
            EnumValue("blue") -> DomainElement(2, C)
        )
        mapping should be (expected)
    }
    
    test("elimination") {
        val theory = Theory.empty
            .withEnumSort(A, EnumValue("cat"), EnumValue("dog"), EnumValue("mouse"))
            .withSort(B)
            .withEnumSort(C, EnumValue("red"), EnumValue("blue"))
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
            .withAxiom(Forall(x of B,
                Not(App("f", EnumValue("cat"), x) === EnumValue("blue"))))
        
        val expected = Theory.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
            .withAxiom(Forall(x of B,
                Not(App("f", DomainElement(1, A), x) === DomainElement(2, C))))
        
        val transformer = EnumsToDEsTransformer
        val result = transformer(ProblemState(theory))
        result.theory should be (expected)
        result.scopes should be (Map(A -> ExactScope(3, true), C -> ExactScope(2, true)))
    }
    
}
