import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner


import fortress.msfol._
import fortress.transformers._
import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class EnumEliminationTests extends FunSuite with Matchers {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    
    val x = Var("x")
    
    test("compute appropriate mapping") {
        val theory = Theory.empty
            .withEnumSort(A, Seq(EnumValue("cat"), EnumValue("dog"), EnumValue("mouse")))
            .withSort(B)
            .withEnumSort(C, Seq(EnumValue("red"), EnumValue("blue")))
        
        val mapping = ( new EnumEliminationTransformer ).computeEnumSortMapping(theory)
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
            .withEnumSort(A, Seq(EnumValue("cat"), EnumValue("dog"), EnumValue("mouse")))
            .withSort(B)
            .withScope(B, 4)
            .withEnumSort(C, Seq(EnumValue("red"), EnumValue("blue")))
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
            .withAxiom(Forall(x of B,
                Not(App("f", EnumValue("cat"), x) === EnumValue("blue"))))
        
        val expected = Theory.empty
            .withSorts(A, B, C)
            .withScope(A, 3)
            .withScope(B, 4)
            .withScope(C, 2)
            .withFunctionDeclaration(FuncDecl("f", A, B, C))
            .withAxiom(Forall(x of B,
                Not(App("f", DomainElement(1, A), x) === DomainElement(2, C))))
        
        val transformer = new EnumEliminationTransformer
        transformer(theory) should be (expected)
    }
    
}
