import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.symmetry._ 

class SymmetryBreakTests_RDD extends UnitSuite {
    
    val A: Sort = SortConst("A")
    val B: Sort = SortConst("B")
    val D: Sort = SortConst("D")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    val c3 = Var("c3")
    val c4 = Var("c4")
    val c5 = Var("c5")
    
    def DE(index: Int, sort: Sort) = DomainElement(index, sort)

    test("rdd Functions - Unused First, Pure, Unary") {
        val f = FuncDecl("f", A, A)
        
        val usedResultValues = IndexedSeq()
        
        val scopes = Map(A -> 9)
        val used = Map(A -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f1A = for(i <- Seq(1, 2)) yield {App("f", DE(1, A)) === DE(i, A)}
        val f2A = for(i <- Seq(1, 2, 3)) yield {App("f", DE(2, A)) === DE(i, A)}
        val f3A = for(i <- Seq(1, 2, 3, 4)) yield {App("f", DE(3, A)) === DE(i, A)}
        val f4A = for(i <- Seq(1, 2, 3, 4, 5)) yield {App("f", DE(4, A)) === DE(i, A)}
        val f5A = for(i <- Seq(1, 2, 3, 4, 5, 6)) yield {App("f", DE(5, A)) === DE(i, A)}
        val f6A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7)) yield {App("f", DE(6, A)) === DE(i, A)}
        val f7A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7, 8)) yield {App("f", DE(7, A)) === DE(i, A)}
        val f8A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7, 8, 9)) yield {App("f", DE(8, A)) === DE(i, A)}
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UnusedFirst(f, deView) map (_.asFormula)
        constraints should have size 8
        constraints should contain (OrList(f1A))
        constraints should contain (OrList(f2A))
        constraints should contain (OrList(f3A))
        constraints should contain (OrList(f4A))
        constraints should contain (OrList(f5A))
        constraints should contain (OrList(f6A))
        constraints should contain (OrList(f7A))
        constraints should contain (OrList(f8A))
    }

    test("rdd Functions - Unused First, Unary") {
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
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UnusedFirst(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f2A))
        constraints should contain (OrList(f5A))
        constraints should contain (OrList(f7A))
        constraints should contain (OrList(f8A))
    }
    
    test("rdd Functions - Unused First, Binary, Single-sort") {
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
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UnusedFirst(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f22))
        constraints should contain (OrList(f55))
        constraints should contain (OrList(f77))
        constraints should contain (OrList(f88))
    }
    
    test("rdd Functions - Unused First, 4-ary, Multi-sort") {
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
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UnusedFirst(f, deView) map (_.asFormula)
        constraints should have size 4
        constraints should contain (OrList(f2121))
        constraints should contain (OrList(f5151))
        constraints should contain (OrList(f7171))
        constraints should contain (OrList(f8181))
    }

    test("rdd Functions - Used First, Pure, Unary") {
        val f = FuncDecl("f", A, A)
        
        val usedResultValues = IndexedSeq()
        
        val scopes = Map(A -> 9)
        val used = Map(A -> usedResultValues)
        val deView = DomainElementUsageView(scopes, used)
        
        val f1A = for(i <- Seq(1, 2)) yield {App("f", DE(1, A)) === DE(i, A)}
        val f2A = for(i <- Seq(1, 2, 3)) yield {App("f", DE(2, A)) === DE(i, A)}
        val f3A = for(i <- Seq(1, 2, 3, 4)) yield {App("f", DE(3, A)) === DE(i, A)}
        val f4A = for(i <- Seq(1, 2, 3, 4, 5)) yield {App("f", DE(4, A)) === DE(i, A)}
        val f5A = for(i <- Seq(1, 2, 3, 4, 5, 6)) yield {App("f", DE(5, A)) === DE(i, A)}
        val f6A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7)) yield {App("f", DE(6, A)) === DE(i, A)}
        val f7A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7, 8)) yield {App("f", DE(7, A)) === DE(i, A)}
        val f8A = for(i <- Seq(1, 2, 3, 4, 5, 6, 7, 8, 9)) yield {App("f", DE(8, A)) === DE(i, A)}
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UsedFirst(f, deView) map (_.asFormula)
        constraints should have size 8
        constraints should contain (OrList(f1A))
        constraints should contain (OrList(f2A))
        constraints should contain (OrList(f3A))
        constraints should contain (OrList(f4A))
        constraints should contain (OrList(f5A))
        constraints should contain (OrList(f6A))
        constraints should contain (OrList(f7A))
        constraints should contain (OrList(f8A))
    }

    test("rdd Functions - Used First, Unary") {
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
        
        val f1A = for(i <- Seq(1, 3, 4, 6, 2)) yield {App("f", DE(1, A)) === DE(i, A)}
        val f3A = for(i <- Seq(1, 3, 4, 6, 2, 5)) yield {App("f", DE(3, A)) === DE(i, A)}
        val f4A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7)) yield {App("f", DE(4, A)) === DE(i, A)}
        val f6A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8)) yield {App("f", DE(6, A)) === DE(i, A)}
        val f2A = for(i <- Seq(1, 3, 4, 6, 2, 5, 7, 8, 9)) yield {App("f", DE(2, A)) === DE(i, A)}
        
        val constraints = Symmetry.rddFunctionRangeRestrictions_UsedFirst(f, deView) map (_.asFormula)
        constraints should have size 5
        constraints should contain (OrList(f1A))
        constraints should contain (OrList(f3A))
        constraints should contain (OrList(f4A))
        constraints should contain (OrList(f6A))
        constraints should contain (OrList(f2A))
    }
}