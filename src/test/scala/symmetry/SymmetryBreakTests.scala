import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.symmetry._ 

class SymmetryBreakTests extends UnitSuite {
    
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
        
        val scopes = Map(B -> 7)
        val used = Map(B -> usedValues)
        val deView = DomainElementUsageView(scopes, used)
        
        Symmetry.csConstantRangeRestrictions(B, constants, deView) map (_.asFormula) should be (
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
        
        val scopes = Map(B -> 7)
        val used = Map(B -> usedValues)
        val deView = DomainElementUsageView(scopes, used)
        
        Symmetry.csConstantImplications(B, constants, deView) should be (
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
        
        val scopes = Map(B -> 7)
        val used = Map(B -> usedValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val constraints = Symmetry.csConstantImplicationsSimplified(B, constants, deView)
        constraints should have size 6
        
        constraints should contain { (c2 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1)) }
        
        constraints should contain { (c3 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1, c2)) }
        constraints should contain { (c3 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(c2)) }
        
        constraints should contain { (c4 === DE(4, B)) ==> (DE(2, B) equalsOneOfFlip Seq(c1, c2, c3)) }
        constraints should contain { (c4 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(c2, c3)) }
        constraints should contain { (c4 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(c3)) }
    }
    
    test("DRD Unary - Equalities") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7
        
        val scopes = Map(A -> 8, B -> 7)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f1A = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A)) === DE(i, B)}
        val f2A = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A)) === DE(i, B)}
        val f3A = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(3, A)) === DE(i, B)}
        val f4A = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(4, A)) === DE(i, B)}
        
        Symmetry.drdFunctionRangeRestrictions(f, deView) map (_.asFormula) should be (
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
        ) // Unused: 1, 4, 6, 7, 8, 9
        
        val scopes = Map(A -> 2, D -> 2, B -> 9)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f111 = for (i <- Seq(2, 3, 5, 1)) yield {App("f", DE(1, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f211 = for (i <- Seq(2, 3, 5, 1, 4)) yield {App("f", DE(2, A), DE(1, D), DE(1, A)) === DE(i, B)}
        val f121 = for (i <- Seq(2, 3, 5, 1, 4, 6)) yield {App("f", DE(1, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f221 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7)) yield {App("f", DE(2, A), DE(2, D), DE(1, A)) === DE(i, B)}
        val f112 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8)) yield {App("f", DE(1, A), DE(1, D), DE(2, A)) === DE(i, B)}
        val f212 = for (i <- Seq(2, 3, 5, 1, 4, 6, 7, 8, 9)) yield {App("f", DE(2, A), DE(1, D), DE(2, A)) === DE(i, B)}
        
        val constraints = Symmetry.drdFunctionRangeRestrictions(f, deView) map (_.asFormula)
        constraints should have size 6
        constraints should contain (OrList(f111))
        constraints should contain (OrList(f211))
        constraints should contain (OrList(f121))
        constraints should contain (OrList(f221))
        constraints should contain (OrList(f112))
        constraints should contain (OrList(f212))
    }
    
    test("DRD Unary - Implications") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7
        
        val scopes: Map[Sort, Int] = Map(A -> 8, B -> 7)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f1A = App("f", DE(1, A))
        val f2A = App("f", DE(2, A))
        val f3A = App("f", DE(3, A))
        val f4A = App("f", DE(4, A))
        
        val constraints = Symmetry.drdFunctionImplications(f, deView)
        constraints should have size 6
        
        constraints should contain { (f2A === DE(4, B)) ==> (f1A === DE(1, B)) }
        
        constraints should contain { (f3A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A)) }
        constraints should contain { (f3A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f1A, f2A)) }
        
        constraints should contain { (f4A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A, f3A)) }
        constraints should contain { (f4A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f1A, f2A, f3A)) }
        constraints should contain { (f4A === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f1A, f2A, f3A)) }
    }
    
    test("DRD Ternary - Implications") {
        val f = FuncDecl("f", A, D, A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9
        
        val scopes = Map(A -> 2, D -> 2, B -> 9)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f111 = App("f", DE(1, A), DE(1, D), DE(1, A))
        val f211 = App("f", DE(2, A), DE(1, D), DE(1, A))
        val f121 = App("f", DE(1, A), DE(2, D), DE(1, A))
        val f221 = App("f", DE(2, A), DE(2, D), DE(1, A))
        val f112 = App("f", DE(1, A), DE(1, D), DE(2, A))
        val f212 = App("f", DE(2, A), DE(1, D), DE(2, A))
        
        val constraints = Symmetry.drdFunctionImplications(f, deView)
        constraints should have size 15
        constraints should contain { (f211 === DE(4, B)) ==> (f111 === DE(1, B)) }
        
        constraints should contain { (f121 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211)) }
        constraints should contain { (f121 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f111, f211)) }
        
        constraints should contain { (f221 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121)) }
        constraints should contain { (f221 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f111, f211, f121)) }
        constraints should contain { (f221 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f111, f211, f121)) }
        
        constraints should contain { (f112 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121, f221)) }
        constraints should contain { (f112 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f111, f211, f121, f221)) }
        constraints should contain { (f112 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f111, f211, f121, f221)) }
        constraints should contain { (f112 === DE(8, B)) ==> (DE(7, B) equalsOneOfFlip Seq(f111, f211, f121, f221)) }
        
        constraints should contain { (f212 === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(8, B)) ==> (DE(7, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
        constraints should contain { (f212 === DE(9, B)) ==> (DE(8, B) equalsOneOfFlip Seq(f111, f211, f121, f221, f112)) }
    }
    
    test("DRD Unary - Implications, Simplified") {
        val f = FuncDecl("f", A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7
        
        val scopes: Map[Sort, Int] = Map(A -> 8, B -> 7)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f1A = App("f", DE(1, A))
        val f2A = App("f", DE(2, A))
        val f3A = App("f", DE(3, A))
        val f4A = App("f", DE(4, A))
        
        val constraints = Symmetry.drdFunctionImplicationsSimplified(f, deView)
        
        constraints should have size 6
        
        constraints should contain { (f2A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A)) }
        
        constraints should contain { (f3A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A)) }
        constraints should contain { (f3A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f2A)) }
        
        constraints should contain { (f4A === DE(4, B)) ==> (DE(1, B) equalsOneOfFlip Seq(f1A, f2A, f3A)) }
        constraints should contain { (f4A === DE(6, B)) ==> (DE(4, B) equalsOneOfFlip Seq(f2A, f3A)) }
        constraints should contain { (f4A === DE(7, B)) ==> (DE(6, B) equalsOneOfFlip Seq(f3A)) }
    }
    
    test("DRD Ternary - Implications, Simplified") {
        val f = FuncDecl("f", A, D, A, B)
        
        val usedResultValues = IndexedSeq(
            DE(2, B),
            DE(3, B),
            DE(5, B),
        ) // Unused: 1, 4, 6, 7, 8, 9
        
        val scopes = Map(A -> 2, D -> 2, B -> 9)
        val used = Map(B -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f111 = App("f", DE(1, A), DE(1, D), DE(1, A))
        val f211 = App("f", DE(2, A), DE(1, D), DE(1, A))
        val f121 = App("f", DE(1, A), DE(2, D), DE(1, A))
        val f221 = App("f", DE(2, A), DE(2, D), DE(1, A))
        val f112 = App("f", DE(1, A), DE(1, D), DE(2, A))
        val f212 = App("f", DE(2, A), DE(1, D), DE(2, A))
        
        val constraints = Symmetry.drdFunctionImplicationsSimplified(f, deView)
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
    
    test("Old Predicates - Unary") {
        val P = FuncDecl("P", A, BoolSort)
        
        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9
        
        val usedValues = Map(A -> usedValsA)
        val scopes = Map(A -> 9)
        val deView = DomainElementUsageView(scopes, usedValues)
        
        val constraints = Symmetry.predicateImplications_OLD(P, deView)
        constraints should have size 5
        constraints should contain (App("P", DE(4, A)) ==> App("P", DE(3, A)))
        constraints should contain (App("P", DE(6, A)) ==> App("P", DE(4, A)))
        constraints should contain (App("P", DE(7, A)) ==> App("P", DE(6, A)))
        constraints should contain (App("P", DE(8, A)) ==> App("P", DE(7, A)))
        constraints should contain (App("P", DE(9, A)) ==> App("P", DE(8, A)))
    }
    
    test("Old Predicates - Ternary, MultiSort") {
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
        val scopes = Map(A -> 9, B -> 8)
        val deView = DomainElementUsageView(scopes, usedValues)
        
        val constraints = Symmetry.predicateImplications_OLD(P, deView)
        constraints should have size 4
        constraints should contain (App("P", DE(4, A), DE(5, B), DE(4, A)) ==> (App("P", DE(3, A), DE(1, B), DE(3, A)))) 
        constraints should contain (App("P", DE(6, A), DE(6, B), DE(6, A)) ==> (App("P", DE(4, A), DE(5, B), DE(4, A)))) 
        constraints should contain (App("P", DE(7, A), DE(7, B), DE(7, A)) ==> (App("P", DE(6, A), DE(6, B), DE(6, A)))) 
        constraints should contain (App("P", DE(8, A), DE(8, B), DE(8, A)) ==> (App("P", DE(7, A), DE(7, B), DE(7, A))))
    }
    
    test("Predicates - Unary") {
        val P = FuncDecl("P", A, BoolSort)
        
        val usedValsA = IndexedSeq(
            DE(1, A),
            DE(2, A),
            DE(5, A)
        ) // Unused 3, 4, 6, 7, 8, 9
        
        val usedValues = Map(A -> usedValsA)
        val scopes = Map(A -> 9)
        
        val constraints = Symmetry.predicateImplications(P, scopes, usedValues)
        constraints should have size 5
        constraints should contain (App("P", DE(4, A)) ==> App("P", DE(3, A)))
        constraints should contain (App("P", DE(6, A)) ==> App("P", DE(4, A)))
        constraints should contain (App("P", DE(7, A)) ==> App("P", DE(6, A)))
        constraints should contain (App("P", DE(8, A)) ==> App("P", DE(7, A)))
        constraints should contain (App("P", DE(9, A)) ==> App("P", DE(8, A)))
    }
    
    test("Predicates - Ternary, MultiSort") {
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
        val scopes = Map(A -> 9, B -> 8)
        
        val constraints = Symmetry.predicateImplications(P, scopes, usedValues)
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
    
    test("CS Functions - Unary, Equality") {
        val f = FuncDecl("f", A, A)
        
        val usedResultValues = IndexedSeq(
            DE(1, A),
            DE(3, A),
            DE(4, A),
            DE(6, A)
        ) // Unused 2 5 7 8 9
        
        val scopes = Map(A -> 9)
        val used = Map(A -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f2A = for(i <- Seq(1, 3, 4, 6, 2, 5)) yield {App("f", DE(2, A)) === DE(i, A)}
        val f5A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7)) yield {App("f", DE(5, A)) === DE(i, A)}
        val f7A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8)) yield {App("f", DE(7, A)) === DE(i, A)}
        val f8A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8, 9)) yield {App("f", DE(8, A)) === DE(i, A)}
        
        val constraints = Symmetry.csFunctionExtRangeRestrictions(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f2A))
        constraints should contain (OrList(f5A))
        constraints should contain (OrList(f7A))
        constraints should contain (OrList(f8A))
    }
    
    test("CS Functions - Binary, Single-sort, Equality") {
        val f = FuncDecl("f", A, A, A)
        
        val usedResultValues = IndexedSeq(
            DE(1, A),
            DE(3, A),
            DE(4, A),
            DE(6, A)
        ) // Unused 2 5 7 8 9
        
        val scopes = Map(A -> 9)
        val used = Map(A -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f22 = for(i <- Seq(1, 3, 4, 6, 2, 5)) yield {App("f", DE(2, A), DE(2, A)) === DE(i, A)}
        val f55 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7)) yield {App("f", DE(5, A), DE(5, A)) === DE(i, A)}
        val f77 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8)) yield {App("f", DE(7, A), DE(7, A)) === DE(i, A)}
        val f88 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8, 9)) yield {App("f", DE(8, A), DE(8, A)) === DE(i, A)}
        
        val constraints = Symmetry.csFunctionExtRangeRestrictions(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f22))
        constraints should contain (OrList(f55))
        constraints should contain (OrList(f77))
        constraints should contain (OrList(f88))
    }
    
    test("CS Functions - 4-ary, Multi-sort, Equality") {
        val f = FuncDecl("f", A, D, A, B, A)
        
        val usedResultValues = IndexedSeq(
            DE(1, A),
            DE(3, A),
            DE(4, A),
            DE(6, A)
        ) // Unused 2 5 7 8 9
        
        val scopes = Map(A -> 9)
        val used = Map(A -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f2121 = for(i <- Seq(1, 3, 4, 6, 2, 5)) yield {App("f", DE(2, A), DE(1, D), DE(2, A), DE(1, B)) === DE(i, A)}
        val f5151 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7)) yield {App("f", DE(5, A), DE(1, D), DE(5, A), DE(1, B)) === DE(i, A)}
        val f7171 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8)) yield {App("f", DE(7, A), DE(1, D), DE(7, A), DE(1, B)) === DE(i, A)}
        val f8181 = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8, 9)) yield {App("f", DE(8, A), DE(1, D), DE(8, A), DE(1, B)) === DE(i, A)}
        
        val constraints = Symmetry.csFunctionExtRangeRestrictions(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f2121))
        constraints should contain (OrList(f5151))
        constraints should contain (OrList(f7171))
        constraints should contain (OrList(f8181))
    }
}
