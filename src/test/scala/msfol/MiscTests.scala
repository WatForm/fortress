import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._

@RunWith(classOf[JUnitRunner])
class MiscTests extends FunSuite with Matchers {
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    
    test("variable as domain element") {
        Var("x").asDomainElement should be (None)
        Var("@12Foo").asDomainElement should be (Some(DomainElement(12, Sort.mkSortConst("Foo"))))
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
    
