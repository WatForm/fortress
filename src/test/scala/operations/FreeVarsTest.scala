import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._

class FreeVarsTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val c = Term.mkVar("c")
    val p = Term.mkVar("p")
    val q = Term.mkVar("q")
    
    val t1 = And(
        App("R", x),
        Not(
            Implication(
                App("Q", y),
                App("R", x)
            )
        )
    )
    
    test("simple term") {
        t1.freeVarConstSymbols should be (Set(x, y))
        t1.freeVars(Signature.empty) should be (Set(x, y))
    }
    
    test("quantified term") {
        val t2 = Forall(Seq(x of A, y of B), Implication(t1, z))
        t2.freeVarConstSymbols should be (Set(z))
        t2.freeVars(Signature.empty) should be (Set(z))
    }
    
    test("constants not free") {
        val sig = Signature.empty
            .withSort(A)
            .withConstant(c of A)
            .withConstant(p of (Sort.Bool))
            
        val t = And(
            Eq(c, x),
            Implication(p, q)
        )
        
        t.freeVarConstSymbols should be (Set(c, x, p, q))
        t.freeVars(sig) should be (Set(x, q))
    }
}
