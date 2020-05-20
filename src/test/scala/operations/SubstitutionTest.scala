import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.operations.TermOps._

@RunWith(classOf[JUnitRunner])
class SubstitutionTest extends FunSuite with Matchers {
    
    def assertAlphaEquivalent(actual: Term, expected: Term): Unit = {
        assert(actual alphaEquivalent expected,
            actual.toString + "\n is not alpha equivalent to \n" + expected.toString,
        )
    }
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val w = Term.mkVar("w")
    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val b = Term.mkVar("b")
    val c = Term.mkVar("c")
    val p = Term.mkVar("p")
    val q = Term.mkVar("q")
    
    val _1 = Term.mkVar("_1")
    val _2 = Term.mkVar("_2")
    
    test("basic substitution") {
        val t = p ==> (x === App("f", y))
        val expected = p ==> (App("h", z) === App("f", y))
        t.substitute(x, App("h", z)) should be (expected)
    }
    
    test("bound variable should not be substituted") {
        val t1 = And(x === x, Exists(x of A, App("R", x)))
                       
        val t2 = And(x === x, Forall(x of A, Term.mkApp("R", x)))
                       
        val e1 = And(Bottom === Bottom, Exists(x of A, App("R", x)))
                      
        val e2 = And(Bottom === Bottom, Forall(x of A, App("R", x)))
                      
        t1.substitute(x, Bottom) should be (e1)
        t2.substitute(x, Bottom) should be (e2)
    }
    
    test("variable capture basic") {
        val t1 = Exists(x of A, x === y)
        val t2 = Forall(x of A, x === y)
        
        val e1 = Exists(z of A, z === x)
        val e2 = Forall(z of A, z === x)
        
        val r1 = t1.substitute(y, x)
        val r2 = t2.substitute(y, x)
        assertAlphaEquivalent(r1, e1)
        assertAlphaEquivalent(r2, e2)
    }
    
    test("variable capture multivar quantifier") {
        val t1 = Exists(Seq(x of A, y of B), App("P", x, y, z))
        val t2 = Forall(Seq(x of A, y of B), App("P", x, y, z))
        
        val expected1 = Exists(Seq(x of A, w of B), App("P", x, w, y))
        val expected2 = Forall(Seq(w of A, y of B), App("P", w, y, x))
        
        assertAlphaEquivalent(t1.substitute(z, y), expected1)
        assertAlphaEquivalent(t2.substitute(z, x), expected2)
    }
    
    test("variable capture complex") {
        val t = Or(
            Forall(x of A, And(
                App("Q", x),
                Exists(x of A, App("P", x, y)))),
            App("Q", y))
        
        val expected = Or(
            Forall(z of A, And(
                App("Q", z),
                Exists(w of A, App("P", w, x)))),
            App("Q", x))
        
        assertAlphaEquivalent(t.substitute(y, x), expected);
    }
    
}
