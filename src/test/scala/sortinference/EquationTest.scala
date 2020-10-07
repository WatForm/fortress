import org.scalatest._
import org.scalactic.Equality

import fortress.msfol._
import fortress.sortinference._

class EquationTest extends UnitSuite {

    // Allows equations to be considered equal even if their arguments are in the opposite order
    implicit val equationEq = new Equality[Equation] {
        def areEqual(a: Equation, b: Any): Boolean =
            b match {
                case eq: Equation => { a.x == eq.x && a.y === eq.y } || { a.x == eq.y && a.y == eq.x }
                case _ => false
            }
    }

    def redundant(equation: Equation): Boolean = equation match {
        case Equation(s, t) => s == t
    }

    val Seq(x, y, z, n, m, alpha, beta, charlie) = Seq("X", "Y", "Z", "N", "M", "ALPHA", "BETA", "CHARLIE").map(SortConst(_))
    val Seq(f1, f2, f3, f_OUT) = Seq("F1", "F2", "F3", "F_OUT").map(SortConst(_))
    val g_OUT = SortConst("G_OUT")
    val Seq(h1, h2) = Seq("H1", "H2").map(SortConst(_))
    val Seq(p1, p2) = Seq("P1", "P2").map(SortConst(_))
    val Seq(u1, u_OUT) = Seq("U1", "U_OUT").map(SortConst(_))

    val Seq(c1, c2, c3, c4, c5, c6, c7, c8) = Seq("c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8").map(Var(_))
    val Seq(r1, r2) = Seq("r1", "f2").map(Var(_))
    val Seq(i1, i2) = Seq("i1", "i2").map(Var(_))

    val constantMap = Map(
        "c1" -> x,
        "c2" -> y,
        "c3" -> z,
        "c4" -> n,
        "c5" -> m,
        "c6" -> alpha,
        "c7" -> beta,
        "c8" -> charlie,
        "r1" -> BoolSort,
        "r2" -> BoolSort,
        "i1" -> IntSort,
        "i2" -> IntSort
    )
    val functionMap = Map(
        "f" -> (Seq(f1, f2), f_OUT),
        "g" -> (Seq(BoolSort, IntSort), g_OUT),
        "h" -> (Seq(h1, h2), IntSort),
        "P" -> (Seq(p1, p2), BoolSort),
        "Q" -> (Seq(BoolSort, IntSort), BoolSort),
        "U" -> (Seq(u1), u_OUT)
    )

    val v1 = Var("v1")
    val v2 = Var("v2")
    val v3 = Var("v3")
    val v4 = Var("v4")
    val v5 = Var("v5")

    val t1 = SortConst("T1")
    val t2 = SortConst("T2")
    val t3 = SortConst("T3")
    val t4 = SortConst("T4")

    test("basic uninterpreted constants, functions, and predicates") {
        val ax1 = Forall(v1 of t1, Not(c1 === v1) or c1 === c2)
        val ax2 = App("f", c1, c2) === c2
        val ax3 = Not(App("P", c1, c2))

        val equations = Equation.accumulate(constantMap, functionMap, Set(ax1, ax2, ax3))
        equations should contain (Equation(t1, x)) // ax1
        equations should contain (Equation(x, y)) // ax1
        equations should contain (Equation(x, f1)) // ax2
        equations should contain (Equation(y, f2)) // ax2
        equations should contain (Equation(y, f_OUT)) // ax2
        equations should contain (Equation(x, p1)) // ax3
        equations should contain (Equation(y, p2)) // ax3
        equations.filter(!redundant(_)) should have size (7)
    }

    test("basic builtin sorts") {
        val ax1 = Exists(Seq(v1 of t1, v2 of t2), App("g", v1, c1) === v2)
        val ax2 = App("h", c1, c2) === c3
        val ax3 = App("U", c4) <==> Top
        val ax4 = Not(Bottom ==> c5)
        val ax5 = Exists(v3 of t3, App("U", v3))
        val ax6 = IfThenElse(c6, c7, c8)

        val equations = Equation.accumulate(constantMap, functionMap, Set(ax1, ax2, ax3, ax4, ax5, ax6))
        equations should contain (Equation(t1, BoolSort)) // ax1
        equations should contain (Equation(x, IntSort)) // ax1
        equations should contain (Equation(g_OUT, t2)) // ax1
        equations should contain (Equation(x, h1)) // ax2
        equations should contain (Equation(y, h2)) // ax2
        equations should contain (Equation(IntSort, z)) // ax2
        equations should contain (Equation(u1, n)) // ax3
        equations should contain (Equation(u_OUT, BoolSort)) // ax3
        equations should contain (Equation(BoolSort, m)) // ax4
        equations should contain (Equation(t3, u1)) // ax5
        equations should contain (Equation(BoolSort, u_OUT)) // ax5
        equations should contain (Equation(alpha, BoolSort)) // ax6
        equations should contain (Equation(beta, charlie)) // ax6
        equations.filter(!redundant(_)) should have size (13)
    }
}