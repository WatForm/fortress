import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._

class FastSubstitutionTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val x = Term.mkVar("x")
    val y = Term.mkVar("y")
    val z = Term.mkVar("z")
    val p = Var("p")
    
    val _1 = Term.mkVar("_1")
    val _2 = Term.mkVar("_2")
    
    test("basic substitution") {
        val t1 = p ==> (x === App("f", y))
        val t2 = App("f", x) or App("f", y)
        
        val e1 = p ==> (App("h", z) === App("f", y))
        val e2 = App("f", y) or App("f", p and Not(p))
        
        (t1 fastSubstitute Map(x -> App("h", z)) ) should be (e1)
        (t2 fastSubstitute Map(x -> y, y -> (p and Not(p)))) should be (e2)
    }
    
    test("substitution should not substitute through quantifier") {
        val t1 = (x === x) and (Exists(x of A, App("R", x)))
        val t2 = (x === y) and (Forall(Seq(x of A, y of B), App("R", x, y)))
        
        val e1 = (Bottom === Bottom) and (Exists(x of A, App("R", x)))
        val e2 = (Bottom === Top) and (Forall(Seq(x of A, y of B), App("R", x, y)))
        
        (t1 fastSubstitute Map(x -> Bottom)) should be (e1)
        (t2 fastSubstitute Map(x -> Bottom, y -> Top)) should be (e2)
    }
    
}
