import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._

class SimplificationTest extends UnitSuite {

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")

    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val a1 = Term.mkDomainElement(1, A)
    val a2 = Term.mkDomainElement(2, A)

    test("not simplification") {
        val t1 = Not(Bottom ==> App("f", y))
        val t2 = Not(Not(Not(Bottom)))

        t1.simplify should be(Bottom)
        t2.simplify should be(Top)
    }

    test("and simplification") {
        val t1 = AndList(App("f", y) ==> Top, Top ==> Bottom, Top)
        val t2 = AndList(App("f", y) ==> Top, x === App("f", y), Top)
        val t3 = AndList(Top, Top, Top)

        t1.simplify should be(Bottom)
        t2.simplify should be(x === App("f", y))
        t3.simplify should be(Top)
    }

    test("or simplification") {
        val t1 = OrList(App("f", y) ==> Top, Top ==> Bottom, Bottom)
        val t2 = OrList(App("f", y) ==> Bottom, Not(App("f", y)), Bottom, Not(Top))
        val t3 = OrList(Bottom, Bottom, Bottom)

        t1.simplify should be(Top)
        t2.simplify should be(Not(App("f", y)))
        t3.simplify should be(Bottom)
    }

    test("applications, equals and closures are atomic") {
        val t1 = (App("f", y) ==> Top) === Top
        val t2 = App("f", OrList(Top, Bottom))
        val t3 = Term.mkClosure("R", Bottom <==> Top, IfThenElse(Bottom, Top, App("f", x)))


        t1.simplify should be((App("f", y) ==> Top) === Top)
        t2.simplify should be(App("f", OrList(Top, Bottom)))
        t3.simplify should be(Term.mkClosure("R", Bottom <==> Top, IfThenElse(Bottom, Top, App("f", x))))
    }

    test("equal simplification") {
        val t1 = a1 === a1
        val t2 = a1 === a2
        val t3 = x === x
        val t4 = x === y
        val t5 = DomainElement(3, A).asSmtConstant === DomainElement(3, A).asSmtConstant
        val t6 = DomainElement(3, A).asSmtConstant === DomainElement(4, A).asSmtConstant

        t1.simplify should be(Top)
        t2.simplify should be(Bottom)
        t3.simplify should be(Top)
        t4.simplify should be(x === y)
        t5.simplify should be(Top)
        t6.simplify should be(Bottom)
    }

    test("forall simplification") {
        val t1 = Forall(x of A, App("R", x))
        val t2 = Forall(Seq(x of A, y of B), App("R", x))
        val t3 = Forall(Seq(x of A, y of B), App("R", z))

        val e1 = Forall(x of A, App("R", x))
        val e2 = Forall(x of A, App("R", x))
        val e3 = App("R", z)

        t1.simplify should be(e1)
        t2.simplify should be(e2)
        t3.simplify should be(e3)
    }
}
