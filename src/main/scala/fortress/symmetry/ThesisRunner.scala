package fortress.symmetry
import fortress.msfol._
import fortress.data._
import scala.collection.immutable.Seq
import fortress.transformers._

object ThesisRunner {
    
    def main(args: Array[String]): Unit = {
        val A = Sort.mkSortConst("A")
        val B = Sort.mkSortConst("B")
        val C = Sort.mkSortConst("C")
        val D = Sort.mkSortConst("D")
        
        val scopes = Map(A -> 2, B -> 3, C -> 3, D -> 5)
        
        val x1 = Var("x1")
        val x2 = Var("x2")
        
        val y1 = Var("y1")
        val y2 = Var("y2")
        
        val z1 = Var("z1")
        val z2 = Var("z2")
        
        val f = FuncDecl("f", A, B, C)
        val g = FuncDecl("g", A, D)
        val P = FuncDecl("P", D, BoolSort)
        
        val theory = Theory.empty
            .withSorts(A, B, C, D)
            .withConstants(x1 of A, x2 of A)
            .withConstants(y1 of B, y2 of B)
            .withConstants(z1 of C)
            .withFunctionDeclaration(f)
            .withFunctionDeclaration(g)
            .withFunctionDeclaration(P)
        
        val symmetryBreaker = new SymBreakTransformer(scopes)
        symmetryBreaker(theory)
    }
}
