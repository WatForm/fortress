import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class IntegerTypeCheckTests extends UnitSuite {
    
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
