import org.scalatest._
import org.junit.Assert._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import fortress.msfol._
import fortress.symmetry._

@RunWith(classOf[JUnitRunner])
class MicrostructureComplementTests extends FunSuite with Matchers {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    
    val c1 = Var("c1")
    val c2 = Var("c2")
    
    test("no constraints") {
        val theory = Theory.empty
            .withSorts(A, B)
            .withConstant(c1 of A)
            .withConstant(c2 of B)
            .withFunctionDeclaration(FuncDecl("f", A, B))
        
        val scopes = Map(A -> 2, B -> 2)
        
        val microstructureComplement = new MicrostructureComplement(theory, scopes)
        microstructureComplement.toString should be ("")
    }
}
