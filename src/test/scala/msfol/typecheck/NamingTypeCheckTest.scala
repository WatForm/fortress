import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class NamingTypeCheckTest extends UnitSuite {
    
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
    
    // Naming tests
    
    // TODO need more tests of this style
    // Former bug
    test("clashing var function name") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        val xp = Var("P") // name clashes with function name
        val t = Forall(xp.of(Sort.Bool), xp)
        an [fortress.data.TypeCheckException.NameConflict] should be thrownBy {t.typeCheck(sig)}
    }
    
    test("clashing var sort name") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        val xp = Var("A") // name clashes with type name
        val t = Forall(xp.of(Sort.Bool), xp)
        an [fortress.data.TypeCheckException.NameConflict] should be thrownBy {t.typeCheck(sig)}
    }
    
    
    test("var F Add Func F") {
        // Have a variable named F, then add a function named F
        pending
    }
}
