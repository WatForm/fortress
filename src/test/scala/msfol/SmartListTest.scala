import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._

@RunWith(classOf[JUnitRunner])
class SmartListTest extends FunSuite with Matchers {
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    
    test("Smart Or") {
        Or.smart(Seq()) should be (Bottom)
        Or.smart(Seq(x)) should be (x)
        Or.smart(Seq(x, y)) should be (OrList(x, y))
        Or.smart(Seq(x, y, z)) should be (OrList(x, y, z))
    }
    
    test("Smart And") {
        And.smart(Seq()) should be (Top)
        And.smart(Seq(x)) should be (x)
        And.smart(Seq(x, y)) should be (AndList(x, y))
        And.smart(Seq(x, y, z)) should be (AndList(x, y, z))
    }
}
    
