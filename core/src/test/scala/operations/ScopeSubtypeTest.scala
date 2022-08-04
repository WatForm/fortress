import org.scalatest._

import fortress.msfol._
import fortress.operations.ScopeSubtype
import fortress.operations.TermOps._

class ScopeSubtypeTest extends UnitSuite {

    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")

    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val a1 = Term.mkDomainElement(1, A)
    val a2 = Term.mkDomainElement(2, A)

    val helpMap: Map[Sort, Scope] = Map(
        A -> NonExactScope(3),
        B -> NonExactScope(3)
    )

    test("basic scope subtype") {
        val t1 = AndList(App("f", y) ==> Top, x === App("f", y), Top)
        val t2 = OrList(App("f", y) ==> Bottom, Not(App("f", y)), Bottom, Not(Top))

        ScopeSubtype.addBoundsPredicates(t1, helpMap) should be(t1)
        ScopeSubtype.addBoundsPredicates(t2, helpMap) should be(t2)
    }

    test("forall/exists scope subtype") {
        val t1 = Forall(x of A, App("R", x))
        val t2 = Forall(Seq(x of A, y of B), App("R", x))
        val t3 = Exists(x of A, App("R", z))
        val t4 = Exists(Seq(x of A, y of B), App("R", z))

        val e1 = Forall(x of A, App(ScopeSubtype.subtypePred(A), x) ==> App("R", x))
        val e2 = Forall(Seq(x of A, y of B), (App(ScopeSubtype.subtypePred(A), x) and App(ScopeSubtype.subtypePred(B), y)) ==> App("R", x))
        val e3 = Exists(x of A, App(ScopeSubtype.subtypePred(A), x) and App("R", z))
        val e4 = Exists(Seq(x of A, y of B), AndList(App(ScopeSubtype.subtypePred(A), x), App(ScopeSubtype.subtypePred(B), y), App("R", z)))

        ScopeSubtype.addBoundsPredicates(t1, helpMap) should be(e1)
        ScopeSubtype.addBoundsPredicates(t2, helpMap) should be(e2)
        ScopeSubtype.addBoundsPredicates(t3, helpMap) should be(e3)
        ScopeSubtype.addBoundsPredicates(t4, helpMap) should be(e4)
    }
}
