import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.transformers._
import fortress.msfol.IntegerExtension._

@RunWith(classOf[JUnitRunner])
class IntegerTypeCheckTests extends FunSuite with Matchers {
    
    test("basic integer literal") {
        val sig = Signature.empty.withIntegers
        IntegerLiteral(5).typeCheck(sig).sort should be (IntSort)
    }
    
    test("basic integer literal, integers not in signature") {
        val sig = Signature.empty
        a [fortress.data.TypeCheckException.UndeclaredSort] should be thrownBy (IntegerLiteral(5).typeCheck(sig))
    }
    
    test("basic +, -, *") {
        val sig = Signature.empty.withIntegers
        App(plus, IntegerLiteral(5), IntegerLiteral(6)).typeCheck(sig).sort should be (IntSort)
    }
    
    test("basic +, -, *, integers in signature") {
        val sig = Signature.empty
        a [fortress.data.TypeCheckException] should be thrownBy
            (App(plus, IntegerLiteral(5), IntegerLiteral(6)).typeCheck(sig))
    }
    
    test("quantify integer, integers not in signature") {
        pending
    }
}
