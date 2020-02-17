import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.transformers._

@RunWith(classOf[JUnitRunner])
class IntegerTypeCheckTests extends FunSuite with Matchers {
    
    test("basic integer literal") {
        val sig = Signature.empty
        IntegerLiteral(5).typeCheck(sig).sort should be (IntSort)
    }
    
    test("basic +, -, *") {
        val sig = Signature.empty
        BuiltinApp(IntPlus, IntegerLiteral(5), IntegerLiteral(6)).typeCheck(sig).sort should be (IntSort)
    }
    
    test("quantify integer") {
        pending
    }
}
