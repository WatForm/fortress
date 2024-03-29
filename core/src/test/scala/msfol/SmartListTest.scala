import org.scalatest._

import fortress.msfol._

class SmartListTest extends UnitSuite {
    
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
    
