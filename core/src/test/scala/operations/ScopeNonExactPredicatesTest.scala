import org.scalatest._
import fortress.msfol._
import fortress.operations.ScopeNonExactPredicates
import fortress.operations.TermOps._
import fortress.problemstate.{NonExactScope, Scope}

class ScopeNonExactPredicatesTest extends UnitSuite {

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

        ScopeNonExactPredicates.addBoundsPredicates(t1, helpMap) should be(t1)
        ScopeNonExactPredicates.addBoundsPredicates(t2, helpMap) should be(t2)
    }

    test("forall/exists scope subtype") {
        val t1 = Forall(x of A, App("R", x))
        val t2 = Forall(Seq(x of A, y of B), App("R", x))
        val t3 = Exists(x of A, App("R", z))
        val t4 = Exists(Seq(x of A, y of B), App("R", z))

        val e1 = Forall(x of A, App(ScopeNonExactPredicates.nonExactScopePred(A), x) ==> App("R", x))
        val e2 = Forall(Seq(x of A, y of B), (App(ScopeNonExactPredicates.nonExactScopePred(A), x) and App(ScopeNonExactPredicates.nonExactScopePred(B), y)) ==> App("R", x))
        val e3 = Exists(x of A, App(ScopeNonExactPredicates.nonExactScopePred(A), x) and App("R", z))
        val e4 = Exists(Seq(x of A, y of B), AndList(App(ScopeNonExactPredicates.nonExactScopePred(A), x), App(ScopeNonExactPredicates.nonExactScopePred(B), y), App("R", z)))

        ScopeNonExactPredicates.addBoundsPredicates(t1, helpMap) should be(e1)
        ScopeNonExactPredicates.addBoundsPredicates(t2, helpMap) should be(e2)
        ScopeNonExactPredicates.addBoundsPredicates(t3, helpMap) should be(e3)
        ScopeNonExactPredicates.addBoundsPredicates(t4, helpMap) should be(e4)
    }
}
