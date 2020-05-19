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
}
    
