import org.scalatest._
import fortress.msfol._
import fortress.problemstate.ExactScope
import fortress.symmetry._

class SymmetryBreakDLTests_Predicates extends UnitSuite {
    
    val A: Sort = SortConst("A")
    val B: Sort = SortConst("B")
    val D: Sort = SortConst("D")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val c5 = Var("c5")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)

    test("Predicates - Unary (Without Disjuncts Limit)") {
        val P = FuncDecl("P", A, BoolSort)
        
        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9
        
        val usedValues = Map(A -> usedValsA)
        val scopes = Map(A -> ExactScope(9))
        val state = StalenessState(Set(A), scopes, usedValues)
        
        val constraints = SymmetryDL.predicateImplications(P, state)
        constraints should have size 5
        constraints should contain (App("P", DE(4, A)) ==> App("P", DE(3, A)))
        constraints should contain (App("P", DE(6, A)) ==> App("P", DE(4, A)))
        constraints should contain (App("P", DE(7, A)) ==> App("P", DE(6, A)))
        constraints should contain (App("P", DE(8, A)) ==> App("P", DE(7, A)))
        constraints should contain (App("P", DE(9, A)) ==> App("P", DE(8, A)))
    }
    
    test("Predicates - Ternary, MultiSort (Without Disjuncts Limit)") {
        val P = FuncDecl("P", A, B, A, BoolSort)
        
        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9
        
        val usedValsB = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(4, B)
        ) // Unused 1, 5, 6, 7, 8
        
        val usedValues = Map(A -> usedValsA, B -> usedValsB)
        val scopes = Map(A -> ExactScope(9), B -> ExactScope(8))
        val state = StalenessState(Set(A, B), scopes, usedValues)
        
        val constraints = SymmetryDL.predicateImplications(P, state)
        constraints should have size 8
        // A constraints
        constraints should contain (App("P", DE(4, A), DE(1, B), DE(4, A)) ==> (App("P", DE(3, A), DE(1, B), DE(3, A))))
        constraints should contain (App("P", DE(6, A), DE(1, B), DE(6, A)) ==> (App("P", DE(4, A), DE(1, B), DE(4, A)))) 
        constraints should contain (App("P", DE(7, A), DE(1, B), DE(7, A)) ==> (App("P", DE(6, A), DE(1, B), DE(6, A))))
        constraints should contain (App("P", DE(8, A), DE(1, B), DE(8, A)) ==> (App("P", DE(7, A), DE(1, B), DE(7, A))))
        constraints should contain (App("P", DE(9, A), DE(1, B), DE(9, A)) ==> (App("P", DE(8, A), DE(1, B), DE(8, A))))
        // B constraints - note that now 1B has been used... so now just 5, 6, 7, 8
        constraints should contain (App("P", DE(1, A), DE(6, B), DE(1, A)) ==> (App("P", DE(1, A), DE(5, B), DE(1, A)))) 
        constraints should contain (App("P", DE(1, A), DE(7, B), DE(1, A)) ==> (App("P", DE(1, A), DE(6, B), DE(1, A)))) 
        constraints should contain (App("P", DE(1, A), DE(8, B), DE(1, A)) ==> (App("P", DE(1, A), DE(7, B), DE(1, A)))) 
    }


    test("Predicates - Unary (With Disjuncts Limit)") {
        val P = FuncDecl("P", A, BoolSort)

        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9

        val usedValues = Map(A -> usedValsA)
        val scopes = Map(A -> ExactScope(9))
        val state = StalenessState(Set(A), scopes, usedValues)

        val constraints = SymmetryDL.predicateImplications(P, state, Some(3))
        constraints should have size 3
        constraints should contain(App("P", DE(4, A)) ==> App("P", DE(3, A)))
        constraints should contain(App("P", DE(6, A)) ==> App("P", DE(4, A)))
        constraints should contain(App("P", DE(7, A)) ==> App("P", DE(6, A)))
    }

    test("Predicates - Ternary, MultiSort  (With Disjuncts Limit)") {
        val P = FuncDecl("P", A, B, A, BoolSort)

        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9

        val usedValsB = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(4, B)
        ) // Unused 1, 5, 6, 7, 8

        val usedValues = Map(A -> usedValsA, B -> usedValsB)
        val scopes = Map(A -> ExactScope(9), B -> ExactScope(8))
        val state = StalenessState(Set(A, B), scopes, usedValues)

        val constraints = SymmetryDL.predicateImplications(P, state, Some(3))
        constraints should have size 6
        // A constraints
        constraints should contain(App("P", DE(4, A), DE(1, B), DE(4, A)) ==> (App("P", DE(3, A), DE(1, B), DE(3, A))))
        constraints should contain(App("P", DE(6, A), DE(1, B), DE(6, A)) ==> (App("P", DE(4, A), DE(1, B), DE(4, A))))
        constraints should contain(App("P", DE(7, A), DE(1, B), DE(7, A)) ==> (App("P", DE(6, A), DE(1, B), DE(6, A))))
        // B constraints - note that now 1B has been used... so now just 5, 6, 7, 8
        constraints should contain(App("P", DE(1, A), DE(6, B), DE(1, A)) ==> (App("P", DE(1, A), DE(5, B), DE(1, A))))
        constraints should contain(App("P", DE(1, A), DE(7, B), DE(1, A)) ==> (App("P", DE(1, A), DE(6, B), DE(1, A))))
        constraints should contain(App("P", DE(1, A), DE(8, B), DE(1, A)) ==> (App("P", DE(1, A), DE(7, B), DE(1, A))))
    }
}