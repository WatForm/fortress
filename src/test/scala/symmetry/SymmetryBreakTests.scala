import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.symmetry._
import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class SymmetryBreakTests extends FunSuite with Matchers {
    
    val A = SortConst("A")
    val B = SortConst("B")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val c5 = Var("c5")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)
    
    test("CS Constant Equalities") {
        val constants = IndexedSeq(
            c1 of B,
            c2 of B,
            c3 of B,
            c4 of B,
            c5 of B)
        
        val usedValues = IndexedSeq(
            DE(1, B),
            DE(3, B),
            DE(5, B),
        )
        
        val unusedValues = IndexedSeq(
            DE(2, B),
            DE(4, B),
            DE(6, B)
        )
        
        Symmetry.csConstantEqualities(B, constants, unusedValues, usedValues) should be (
            Set(
                Or(c1 === DE(1, B), c1 === DE(3, B), c1 === DE(5, B), c1 === DE(2, B)),
                Or(c2 === DE(1, B), c2 === DE(3, B), c2 === DE(5, B), c2 === DE(2, B), c2 === DE(4, B)),
                Or(c3 === DE(1, B), c3 === DE(3, B), c3 === DE(5, B), c3 === DE(2, B), c3 === DE(4, B), c3 === DE(6, B)),
            )
        )
    }
}
