import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

class SortInferenceTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    val D = Sort.mkSortConst("D")
    
    val _0 = Sort.mkSortConst("0")
    val _1 = Sort.mkSortConst("1")
    val _2 = Sort.mkSortConst("2")
    val _3 = Sort.mkSortConst("3")
    val _4 = Sort.mkSortConst("4")
    
    test("function, no axioms", ImplSensitive) {
        val f = FuncDecl("f", A, A, A)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
        
        val f_exp = FuncDecl("f", _0, _1, _2)
        val expectedTheory = Theory.empty
            .withSorts(_0, _1, _2)
            .withFunctionDeclarations(f_exp)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, no axioms", ImplSensitive) {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            
        val P_exp = FuncDecl("P", _0, _1, _2, Sort.Bool)
        val expectedTheory = Theory.empty
            .withSorts(_0, _1, _2)
            .withFunctionDeclarations(P_exp)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do not restrict sorts", ImplSensitive) {
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
        
        val f_exp = FuncDecl("f", _0, _1, _2)
        
        val rowConstraint_exp = Forall(Seq(r of _0, c1 of _1, c2 of _1),
            (App("f", r, c1) === App("f", r, c2)) ==> (c1 === c2))
            
        val expectedTheory = Theory.empty
            .withSorts(_0, _1, _2)
            .withFunctionDeclarations(f_exp)
            .withAxiom(rowConstraint_exp)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do not restrict sorts", ImplSensitive) {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val ax = Forall(x of A, Exists(Seq(y of A, z of A), App("P", x, y, z)))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
            
        val P_exp = FuncDecl("P", _0, _1, _2, Sort.Bool)
        
        val ax_exp = Forall(x of _0, Exists(Seq(y of _1, z of _2), App("P", x, y, z)))
        
        val expectedTheory = Theory.empty
            .withSorts(_0, _1, _2)
            .withFunctionDeclarations(P_exp)
            .withAxiom(ax_exp)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do restrict sorts", ImplSensitive) {
        val f = FuncDecl("f", A, A, A)
        val x = Var("x")
        val y = Var("y")
        
        val ax = Forall(Seq(x of A, y of A), App("f", x, y) === y)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(ax)
        
        val f_exp = FuncDecl("f", _0, _2, _2)
        
        val ax_exp = Forall(Seq(x of _0, y of _2), App("f", x, y) === y)
            
        val expectedTheory = Theory.empty
            .withSorts(_0, _2)
            .withFunctionDeclarations(f_exp)
            .withAxiom(ax_exp)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do restrict sorts", ImplSensitive) {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val ax = Forall(x of A, Not(Exists(y of A, App("P", x, y, x))))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
            
        val P_exp = FuncDecl("P", _2, _1, _2, Sort.Bool)
        
        val ax_exp = Forall(x of _2, Not(Exists(y of _1, App("P", x, y, x))))
        
        val expectedTheory = Theory.empty
            .withSorts(_1, _2)
            .withFunctionDeclarations(P_exp)
            .withAxiom(ax_exp)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (expectedTheory)
        substitution(generalTheory) should be (theory)
    }
}
