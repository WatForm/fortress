import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._

class SimplificationWithLearnedLiteralsTest extends UnitSuite {

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")

    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val a1 = Term.mkDomainElement(1, A)
    val a2 = Term.mkDomainElement(2, A)

    test("not simplification with learned literals") {
        val t1 = Not(Not(App("f", x) === App("f", y)))
        val learnedLiterals = Map((App("f", x) === App("f", y)) -> Bottom)

        t1.simplifyWithLearnedLiterals(learnedLiterals) should be(Bottom)
    }

    test("implication simplification with learned literals") {
        val t1 = Top ==> (App("f", x) === App("f", y))
        val t2 = (App("f", x) === App("f", y)) ==> Bottom
        val learnedLiterals = Map((App("f", x) === App("f", y)) -> Bottom)

        t1.simplifyWithLearnedLiterals(learnedLiterals) should be(Bottom)
        t2.simplifyWithLearnedLiterals(learnedLiterals) should be(Top)
    }

    test("iff simplification with learned literals") {
        val t1 = Top <==> (App("f", x) === App("f", y))
        val t2 = (Top <==> (App("f", x) === App("f", y))) <==> Bottom
        val learnedLiterals = Map((App("f", x) === App("f", y)) -> Bottom)

        t1.simplifyWithLearnedLiterals(learnedLiterals) should be(Bottom)
        t2.simplifyWithLearnedLiterals(learnedLiterals) should be(Not(Bottom))
    }

    test("ifThenElse simplification with learned literals") {
        val t1 = IfThenElse(App("f", x), Not(Bottom), App("f", x) === App("f", y))
        val learnedLiterals1 = Map(App("f", x) -> Bottom, (App("f", x) === App("f", y)) -> Bottom)
        val t2 = IfThenElse(App("f", x), Not(Bottom), App("f", x) === App("f", y))
        val learnedLiterals2: Map[Term, LeafTerm] = Map(App("f", x) -> Top)

        t1.simplifyWithLearnedLiterals(learnedLiterals1) should be(Bottom)
        t2.simplifyWithLearnedLiterals(learnedLiterals2) should be(Top)
    }

    test("other terms simplification with learned literals") {
        val t1 = App("f", x) === y
        val learnedLiterals1 = Map((App("f", x) === y) -> y)
        val t2 = Term.mkClosure("R", Bottom <==> Top, IfThenElse(Bottom, Top, App("f", x)))
        val learnedLiterals2 = Map(Term.mkClosure("R", Bottom <==> Top, IfThenElse(Bottom, Top, App("f", x))) -> Bottom)

        t1.simplifyWithLearnedLiterals(learnedLiterals1) should be(y)
        t2.simplifyWithLearnedLiterals(learnedLiterals2) should be(Bottom)
    }
}
