import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class TermStructureTypeCheckTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val p = Var("p")
    val q = Var("q")
    
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)
    val Q = FuncDecl.mkFuncDecl("Q", B, Sort.Bool)
    val f = FuncDecl.mkFuncDecl("f", A, B)
    val g = FuncDecl.mkFuncDecl("g", B, A)
    val h = FuncDecl.mkFuncDecl("h", Sort.Bool, Sort.Bool)
    val R = FuncDecl.mkFuncDecl("R", A, A, Sort.Bool)
    
    // val structure
    
    test("forall inside app") {
        // Forall is not allowed inside an application
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(h)
        val t = App("h", Forall(x.of(A), Top))
        an [fortress.data.TypeCheckException.BadStructure] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    test("exists inside app") {
        // Exists is not allowed inside an application
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(h)
        val t = App("h", Exists(x.of(A), Top))
        an [fortress.data.TypeCheckException.BadStructure] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    // We now allow this
    /*
    test("quantifier inside ite condition") {
        val sig = Signature.empty
            .withSort(A)
            .withConstant(x of A)
        val t = IfThenElse(Exists(y of A, y === y), x, x)
        an [fortress.data.TypeCheckException.BadStructure] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    */
}
