import org.scalatest._

import fortress.msfol._

class MiscTests extends UnitSuite {
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    
    test("variable as domain element") {
        val Foo = Sort.mkSortConst("Foo")
        DomainElement.interpretName("x") should be (None)
        DomainElement.interpretName(DomainElement(12, Foo).asSmtConstant.name) should be (Some(DomainElement(12, Foo)))
    }
    
    test("distinct as pairwise not equals") {
        val t1 = Distinct(x, y, z)
        val t2 = And(
            Not(x === y),
            Not(x === z),
            Not(y === z)
        )
        t1.asInstanceOf[Distinct].asPairwiseNotEquals should be (t2)
    }
}
    
