import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class TypeCheckSanitizeTest extends UnitSuite {
    
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
    
    test("ite return bool, replace with equiv formula") {
        val p = Var("p")
        val q = Var("q")
        val r = Var("r")
        val sig = Signature.empty
            .withConstants(p of BoolSort, q of BoolSort, r of BoolSort)
        
        val t = IfThenElse(p, q, r)
        
        val expected = (p and q) or (Not(p) and r)
        
        val result = t.typeCheck(sig)
        result.sort should be (Sort.Bool)
        result.sanitizedTerm should be (expected)
    }
}
    
