import org.scalatest._

import fortress.msfol._
import fortress.operations._
import fortress.operations.TermOps._


class SimpleUnboundedCheckerTest extends UnitSuite {
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")

    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")


    test("single term test0") {
        val axiom1 = Forall( x of A, App("f", x) ==> Top )
        val expected : Set[Sort] = Set(A)
        SimpleUnboundedChecker.getBoundedSort(axiom1) should be (expected)
    }

    test("single term test1") {
        val axiom1 = Exists( y of B, Forall( x of A, App("f", x) ==> App("P", y) ) )
        val expected : Set[Sort] = Set(A)
        SimpleUnboundedChecker.getBoundedSort(axiom1) should be (expected)
    }

    test("single term test2") {
        val axiom1 = Forall( x of A, Forall( y of B, Or( And(App("f", x), App("P", y)) , Forall( z of C, And(App("P", y),App("Q", z)) ) ) ) )
        val expected : Set[Sort] = Set(A,B,C)
        SimpleUnboundedChecker.getBoundedSort(axiom1) should be (expected)
    }

    test("test") {
        val axiom = Forall(Seq(x.of(A), y.of(A)), Term.mkClosure("closure", x, y) )
        val expected : Set[Sort] = Set(A)
        SimpleUnboundedChecker.getBoundedSort(axiom) should be (expected)
    }

    test("terms set test") {
        val axiom1 = Exists( y of B, Forall( x of A, App("f", x) ==> App("P", y) ) )
        val axiom2 = Not(Forall( z of C, App("Q", z) ==> Bottom ))
        val expected = Set(A,C)
        SimpleUnboundedChecker.getBoundedSort(Seq(axiom1,axiom2)) should be (expected)
    }
}
