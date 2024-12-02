package fortress.util

import fortress.msfol._

object SmartEq {
    // Helper for Equality Generation
    def smartEq(sort: Sort, left: Term, right: Term): Term = {
        sort match {
            case IntSort => BuiltinApp(IntEQ, Seq(left, right))
            case BitVectorSort(bitwidth) => BuiltinApp(BvEQ, Seq(left, right))
            case _ => Eq(left, right)
        }
    }
}