import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

@RunWith(classOf[JUnitRunner])
class TypeCheckSanitizeTest extends FunSuite with Matchers {
    
    // Check that terms are properly sanitized during typechecking
    // Currently this just means replacing boolean = with iff
    
    // Instances of = between booleans should be replaced with iff
    test("bool eq replaced with iff") {
        val A = Sort.mkSortConst("A")
        val x = Var("x")
        val p = Var("p")
        
        val sig = Signature.empty
            .withSort(A)
            .withConstant(x.of(A))
            .withConstant(p.of(Sort.Bool))
            
        val t = And(
            Eq(x, x),
            Eq(p, p)
        )
        
        val expected = And(
            Eq(x, x),
            Iff(p, p)
        )
        
        val result = t.typeCheck(sig)
        result.sort should be (Sort.Bool)
        result.sanitizedTerm should be (expected)
    }
}
    
