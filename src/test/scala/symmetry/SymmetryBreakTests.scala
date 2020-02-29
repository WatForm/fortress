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
    val D = SortConst("D")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val c5 = Var("c5")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)
    
    test("CS Constant - Equalities") {
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
        
        val scope = 7
        
        Symmetry.csConstantEqualities(B, constants, scope, usedValues) should be (
            Set(
                Or(c1 === DE(1, B), c1 === DE(3, B), c1 === DE(5, B), c1 === DE(2, B)),
                Or(c2 === DE(1, B), c2 === DE(3, B), c2 === DE(5, B), c2 === DE(2, B), c2 === DE(4, B)),
                Or(c3 === DE(1, B), c3 === DE(3, B), c3 === DE(5, B), c3 === DE(2, B), c3 === DE(4, B), c3 === DE(6, B)),
                Or(c4 === DE(1, B), c4 === DE(3, B), c4 === DE(5, B), c4 === DE(2, B), c4 === DE(4, B), c4 === DE(6, B), c4 === DE(7, B)),
            )
        )
    }
    
    test("CS Constant - Implications") {
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
        
        val scope = 7
        
        Symmetry.csConstantImplications(B, constants, scope, usedValues) should be (
            Set(
                (c2 === DE(4, B)) ==> (c1 === DE(2, B)),
                (c3 === DE(4, B)) ==> Or(c1 === DE(2, B), c2 === DE(2, B)),
                (c3 === DE(6, B)) ==> Or(c1 === DE(4, B), c2 === DE(4, B)),
                (c4 === DE(4, B)) ==> Or(c1 === DE(2, B), c2 === DE(2, B), c3 === DE(2, B)),
                (c4 === DE(6, B)) ==> Or(c1 === DE(4, B), c2 === DE(4, B), c3 === DE(4, B)),
                (c4 === DE(7, B)) ==> Or(c1 === DE(6, B), c2 === DE(6, B), c3 === DE(6, B))
            )
        )
    }
    
    test("DRD Unary - Equalities") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        )
        
        val scopes: Map[Sort, Int] = Map(A -> 8, B -> 7)
        
        val f1A = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A)) === DE(i, B)}
        val f2A = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A)) === DE(i, B)}
        val f3A = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(3, A)) === DE(i, B)}
        val f4A = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(4, A)) === DE(i, B)}
        
        Symmetry.drdFunctionEqualities(f, scopes, usedResultValues) should be (
            Set(
                OrList(f1A),
                OrList(f2A),
                OrList(f3A),
                OrList(f4A)
            )
        )
    }
    
    test("DRD Ternary - Equalities") {
        val f = FuncDecl("f", A, D, A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        )
        
        val scopes: Map[Sort, Int] = Map(A -> 2, D -> 2, B -> 9)
        
        val f111 = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f211 = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f121 = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(1, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f221 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(2, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f112 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8)) yield {App("f", DE(1, A), DE(1, D), DE(2, A)) === DE(i, B)}
        val f212 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8, 9)) yield {App("f", DE(2, A), DE(1, D), DE(2, A)) === DE(i, B)}
        
        val constraints = Symmetry.drdFunctionEqualities(f, scopes, usedResultValues)
        constraints should have size 6
        constraints should contain (OrList(f111))
        constraints should contain (OrList(f211))
        constraints should contain (OrList(f121))
        constraints should contain (OrList(f221))
        constraints should contain (OrList(f112))
        constraints should contain (OrList(f212))
    }
}
