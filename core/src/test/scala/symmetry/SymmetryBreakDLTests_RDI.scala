import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.symmetry._

class SymmetryBreakDLTests_RDI extends UnitSuite {
    val A: Sort = SortConst("A")
    val B: Sort = SortConst("B")
    val D: Sort = SortConst("D")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val c5 = Var("c5")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)

    test("rdi Unary - Equalities (Without Disjuncts Limit)") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7
        
        val scopes = Map(A -> ExactScope(8), B -> ExactScope(7))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, B), scopes, used)
        
        val f1A = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A)) === DE(i, B)}
        val f2A = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A)) === DE(i, B)}
        val f3A = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(3, A)) === DE(i, B)}
        val f4A = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(4, A)) === DE(i, B)}
        
        SymmetryDL.rdiFunctionRangeRestrictions(f, state) map (_.asFormula) should be (
            Set(
                OrList(f1A),
                OrList(f2A),
                OrList(f3A),
                OrList(f4A)
            )
        )
    }
    
    test("rdi Ternary - Equalities (Without Disjuncts Limit)") {
        val f = FuncDecl("f", A, D, A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9
        
        val scopes = Map(A -> ExactScope(2), D -> ExactScope(2), B -> ExactScope(9))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, D, B), scopes, used)
        
        val f111 = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f211 = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f121 = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(1, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f221 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(2, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f112 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8)) yield {App("f", DE(1, A), DE(1, D), DE(2, A)) === DE(i, B)}
        val f212 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8, 9)) yield {App("f", DE(2, A), DE(1, D), DE(2, A)) === DE(i, B)}
        
        val constraints = SymmetryDL.rdiFunctionRangeRestrictions(f, state) map (_.asFormula)
        constraints should have size 6
        constraints should contain (OrList(f111))
        constraints should contain (OrList(f211))
        constraints should contain (OrList(f121))
        constraints should contain (OrList(f221))
        constraints should contain (OrList(f112))
        constraints should contain (OrList(f212))
    }

    test("rdi Unary - Implications, Simplified (Without Disjuncts Limit)") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7
        
        val scopes: Map[Sort, Scope] = Map(A -> ExactScope(8), B -> ExactScope(7))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, B), scopes, used)
        
        val f1A = App("f", DE(1, A))
        val f2A = App("f", DE(2, A))
        val f3A = App("f", DE(3, A))
        val f4A = App("f", DE(4, A))
        
        val constraints = SymmetryDL.rdiFunctionImplicationsSimplified(f, state)
        
        constraints should have size 6
        
        constraints should contain { (f2A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A)) }
        
        constraints should contain { (f3A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A)) }
        constraints should contain { (f3A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f2A)) }
        
        constraints should contain { (f4A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A, f3A)) }
        constraints should contain { (f4A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f2A, f3A)) }
        constraints should contain { (f4A === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f3A)) }
    }
    
    test("rdi Ternary - Implications, Simplified (Without Disjuncts Limit)") {
        val f = FuncDecl("f", A, D, A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9
        
        val scopes = Map(A -> ExactScope(2), D -> ExactScope(2), B -> ExactScope(9))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, D, B), scopes, used)
        
        val f111 = App("f", DE(1, A), DE(1, D), DE(1, A))
        val f211 = App("f", DE(2, A), DE(1, D), DE(1, A))
        val f121 = App("f", DE(1, A), DE(2, D), DE(1, A))
        val f221 = App("f", DE(2, A), DE(2, D), DE(1, A))
        val f112 = App("f", DE(1, A), DE(1, D), DE(2, A))
        val f212 = App("f", DE(2, A), DE(1, D), DE(2, A))
        
        val constraints = SymmetryDL.rdiFunctionImplicationsSimplified(f, state)
        constraints should have size 15
        constraints should contain { (f211 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111)) }
        
        constraints should contain { (f121 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211)) }
        constraints should contain { (f121 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f211)) }
        
        constraints should contain { (f221 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121)) }
        constraints should contain { (f221 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f211, f121)) }
        constraints should contain { (f221 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f121)) }
        
        constraints should contain { (f112 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121, f221)) }
        constraints should contain { (f112 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f211, f121, f221)) }
        constraints should contain { (f112 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f121, f221)) }
        constraints should contain { (f112 === DE(8, B)) ==> (DE(7, B) equalsOneOfFlip Seq(f221)) }
        
        constraints should contain { (f212 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f121, f221, f112)) }
        constraints should contain { (f212 === DE(8, B)) ==> (DE(7, B) equalsOneOfFlip Seq(f221, f112)) }
        constraints should contain { (f212 === DE(9, B)) ==> (DE(8, B) equalsOneOfFlip Seq(f112)) }
    }

    test("rdi Unary - Equalities (With Disjuncts Limit)") {
        val f = FuncDecl("f", A, B)

        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7

        val scopes = Map(A -> ExactScope(8), B -> ExactScope(7))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, B), scopes, used)

        val f1A = for (i <- Seq(2, 3, 5, 1)) yield {
            App("f", DE(1, A)) === DE(i, B)
        }
        val f2A = for (i <- Seq(2, 3, 5, 1, 4)) yield {
            App("f", DE(2, A)) === DE(i, B)
        }
        val f3A = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {
            App("f", DE(3, A)) === DE(i, B)
        }

        SymmetryDL.rdiFunctionRangeRestrictions(f, state, Some(6)) map (_.asFormula) should be(
            Set(
                OrList(f1A),
                OrList(f2A),
                OrList(f3A)
            )
        )
    }

    test("rdi Ternary - Equalities (With Disjuncts Limit)") {
        val f = FuncDecl("f", A, D, A, B)

        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9

        val scopes = Map(A -> ExactScope(2), D -> ExactScope(2), B -> ExactScope(9))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, D, B), scopes, used)

        val f111 = for (i <- Seq(2, 3, 5, 1)) yield {
            App("f", DE(1, A), DE(1, D), DE(1, A)) === DE(i, B)
        }
        val f211 = for (i <- Seq(2, 3, 5, 1, 4)) yield {
            App("f", DE(2, A), DE(1, D), DE(1, A)) === DE(i, B)
        }
        val f121 = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {
            App("f", DE(1, A), DE(2, D), DE(1, A)) === DE(i, B)
        }

        val constraints = SymmetryDL.rdiFunctionRangeRestrictions(f, state, Some(6)) map (_.asFormula)
        constraints should have size 3
        constraints should contain(OrList(f111))
        constraints should contain(OrList(f211))
        constraints should contain(OrList(f121))
    }

    test("rdi Unary - Implications, Simplified (With Disjuncts Limit)") {
        val f = FuncDecl("f", A, B)

        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7

        val scopes: Map[Sort, Scope] = Map(A -> ExactScope(8), B -> ExactScope(7))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, B), scopes, used)

        val f1A = App("f", DE(1, A))
        val f2A = App("f", DE(2, A))
        val f3A = App("f", DE(3, A))

        val constraints = SymmetryDL.rdiFunctionImplicationsSimplified(f, state, 3)

        constraints should have size 3

        constraints should contain {
            (f2A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A))
        }

        constraints should contain {
            (f3A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A))
        }
        constraints should contain {
            (f3A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f2A))
        }
    }

    test("rdi Ternary - Implications, Simplified (With Disjuncts Limit)") {
        val f = FuncDecl("f", A, D, A, B)

        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9

        val scopes = Map(A -> ExactScope(2), D -> ExactScope(2), B -> ExactScope(9))
        val used = Map(B -> usedResultValues)
        val state = StalenessState(Set(A, D, B), scopes, used)

        val f111 = App("f", DE(1, A), DE(1, D), DE(1, A))
        val f211 = App("f", DE(2, A), DE(1, D), DE(1, A))
        val f121 = App("f", DE(1, A), DE(2, D), DE(1, A))
        val f221 = App("f", DE(2, A), DE(2, D), DE(1, A))

        val constraints = SymmetryDL.rdiFunctionImplicationsSimplified(f, state, 3)
        constraints should have size 3
        constraints should contain {
            (f211 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111))
        }

        constraints should contain {
            (f121 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211))
        }
        constraints should contain {
            (f121 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f211))
        }
    }
}
