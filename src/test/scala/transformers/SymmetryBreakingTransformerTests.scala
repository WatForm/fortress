import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.transformers._

import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class SymmetryBreakingTransformerTests extends FunSuite with Matchers {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    
    val a1 = Var("a1")
    val a2 = Var("a2")
    val a3 = Var("a3")
    val b1 = Var("b1")
    val b2 = Var("b2")
    val b3 = Var("b3")
    val b4 = Var("b4")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)
    
    test("Pure, basic constants") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstants(a1 of A, a2 of A, a3 of A)
            .withConstants(b1 of B, b2 of B, b3 of B, b4 of B)
        
        val e_a1 = a1 === DE(1, A)
        val e_a2 = Or(a2 === DE(1, A), a2 === DE(2, A))
        val e_a3 = Or(a3 === DE(1, A), a3 === DE(2, A), a3 === DE(3, A))
        val e_b1 = b1 === DE(1, B)
        val e_b2 = Or(b2 === DE(1, B), b2 === DE(2, B))
        
        val i1 = (a2 === DE(2, A)) ==> (a1 === DE(1, A))
        val i2 = (a3 === DE(2, A)) ==> Or(a1 === DE(1, A), a2 === DE(1, A))
        val i3 = (a3 === DE(3, A)) ==> Or(a1 === DE(2, A), a2 === DE(2, A))
        val i4 = (b2 === DE(2, B)) ==> (b1 === DE(1, B))
        
        val expected = theory.withAxioms(Seq(e_a1, e_a2, e_a3, e_b1, e_b2))
            .withAxioms(Seq(i1, i2, i3, i4))
        
        val scopes = Map(A -> 4, B -> 2)
        val transformerONE = new SymmetryBreakingTransformerONE(scopes)
        val transformerTWO = new SymmetryBreakingTransformerONE(scopes)
        
        transformerTWO(theory) should be (expected)
    }
    
}
