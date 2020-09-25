import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

class SortInferenceTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    val D = Sort.mkSortConst("D")
    
    val _0 = Sort.mkSortConst("S0")
    val _1 = Sort.mkSortConst("S1")
    val _2 = Sort.mkSortConst("S2")
    val _3 = Sort.mkSortConst("S3")
    val _4 = Sort.mkSortConst("S4")
    
    test("function, no axioms") {
        val f = FuncDecl("f", A, A, A)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, no axioms") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)
        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do not restrict sorts") {
        val f = FuncDecl("f", A, A, A)
        val r = Var("r")
        val r1 = Var("r1")
        val r2 = Var("r2")
        val c = Var("c")
        val c1 = Var("c1")
        val c2 = Var("c2")
        
        val rowConstraint = Forall(Seq(r of A, c1 of A, c2 of A),
            (App("f", r, c1) === App("f", r, c2)) ==> (c1 === c2))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(rowConstraint)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do not restrict sorts") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val ax = Forall(x of A, Exists(Seq(y of A, z of A), App("P", x, y, z)))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)
        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do restrict sorts") {
        val f = FuncDecl("f", A, A, A)
        val x = Var("x")
        val y = Var("y")
        
        // Force 1st input = output
        val ax = Forall(Seq(x of A, y of A), App("f", x, y) === y)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(ax)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do restrict sorts") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        // Force 1st input = 3rd input
        val ax = Forall(x of A, Not(Exists(y of A, App("P", x, y, x))))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        substitution(generalTheory) should be (theory)
    }
    
    test("when theory is already maximally general, return original theory") {
        val f = FuncDecl("f", A, A, A)
        val x = Var("x")
        
        val ax = Forall(x of A, App("f", x, x) === x)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(ax)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (theory)
        substitution shouldBe Symbol("isIdentity")
    }
}
