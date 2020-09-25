import org.scalatest._

import fortress.msfol._
import fortress.sortinference._

class UnificationTest extends UnitSuite {
    val S1 = SortConst("S1")
    val S2 = SortConst("S2")
    val S3 = SortConst("S3")
    val S4 = SortConst("S4")
    val S5 = SortConst("S5")
    val S6 = SortConst("S6")
    val S7 = SortConst("S7")
    val S8 = SortConst("S8")
    val S9 = SortConst("S9")
    val S10 = SortConst("S10")

    test("basic unification") {
        val equations = Set(
            Equation(S1, S2),
            Equation(S2, BoolSort),
            Equation(S3, IntSort),
            Equation(S4, S5),
            Equation(S6, S7),
            Equation(S6, S8),
            Equation(S6, S9),
            Equation(S9, IntSort),
            Equation(S10, S10),
            Equation(IntSort, IntSort)
        )

        val unifier: SortSubstitution = Unification.unify(equations.toList)
        unifier(S1) should be (BoolSort)
        unifier(S2) should be (BoolSort)
        unifier(S3) should be (IntSort)
        unifier(S4) should equal (unifier(S5))
        unifier(S4) should (equal (S4) or equal (S5))
        unifier(S5) should (equal (S4) or equal (S5))
        unifier(S6) should be (IntSort)
        unifier(S7) should be (IntSort)
        unifier(S8) should be (IntSort)
        unifier(S9) should be (IntSort)
        unifier(S10) should be (S10)
        unifier(BoolSort) should be (BoolSort)
        unifier(IntSort) should be (IntSort)
    }
}