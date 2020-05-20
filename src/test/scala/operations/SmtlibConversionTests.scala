import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.operations.TermOps._

@RunWith(classOf[JUnitRunner])
class SmtlibConversionTests extends FunSuite with Matchers {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val f = FuncDecl.mkFuncDecl("f", A, B)
    val P = FuncDecl.mkFuncDecl("P", A, B, Sort.Bool)
    val q = Var("q")
    val r = Var("r")
    
    test("basic conversion") {
        val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
        val formula2 = ((q ==> r) and (r ==> q)) or (Not(r) <==> q)
        val formula3 = Exists(x of A, Forall(y of B, Distinct(x, x) or App("P", x, y)))
        val formula4 = And(Top, Bottom, q, r)
        
        formula1.smtlib should be ("(forall ((x A) (y B)) (= (f x) y))")
        formula2.smtlib should be ("(or (and (=> q r) (=> r q)) (= (not r) q))")
        formula3.smtlib should be ("(exists ((x A)) (forall ((y B)) (or (distinct x x) (P x y))))")
        formula4.smtlib should be ("(and true false q r)")
    }
    
    test("basic assertion") {
         val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
         formula1.smtlibAssertion should be ("(assert (forall ((x A) (y B)) (= (f x) y)))")
    }
    
    test("integer conversion") {
        val l = Var("l")
        val u = Var("u")
        val prime = Var("prime")
        
        val formula = Not(Exists(Seq(x of IntSort, y of IntSort), And(
            BuiltinApp(IntGT, x, IntegerLiteral(1)),
            BuiltinApp(IntGT, y, IntegerLiteral(1)),
            BuiltinApp(IntMult, x, y) === prime
        )))
        
        formula.smtlibAssertion should be ("(assert (not (exists ((x Int) (y Int)) (and (> x 1) (> y 1) (= (* x y) prime)))))")
    }
}
