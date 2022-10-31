import org.scalatest._
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.problemstate.ExactScope
import fortress.symmetry._ 

class SymmetryBreakTests_Constants extends UnitSuite {
    
    val A: Sort = SortConst("A")
    val B: Sort = SortConst("B")
    val D: Sort = SortConst("D")
    
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
        
        val scopes = Map(B -> ExactScope(7))
        val used = Map(B -> usedValues)
        val state = StalenessState(Set(B), scopes, used)
        
        Symmetry.csConstantRangeRestrictions(B, constants, state) map (_.asFormula) should be (
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
        ) // Unused: 2, 4, 6, 7
        
        val scopes = Map(B -> ExactScope(7))
        val used = Map(B -> usedValues)
        val state = StalenessState(Set(B), scopes, used)
        
        Symmetry.csConstantImplications(B, constants, state) should be (
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
    
    test("CS Constant - Implications, Simplified") {
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
        ) // Unused: 2, 4, 6, 7
        
        val scopes = Map(B -> ExactScope(7))
        val used = Map(B -> usedValues)
        val state = StalenessState(Set(B), scopes, used)
        
        val constraints = Symmetry.csConstantImplicationsSimplified(B, constants, state)
        constraints should have size 6
        
        constraints should contain { (c2 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1)) }
        
        constraints should contain { (c3 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1, c2)) }
        constraints should contain { (c3 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(c2)) }
        
        constraints should contain { (c4 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1, c2, c3)) }
        constraints should contain { (c4 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(c2, c3)) }
        constraints should contain { (c4 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(c3)) }
    }
}