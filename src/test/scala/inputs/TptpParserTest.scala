import java.io.{File, FileInputStream}

import fortress.inputs._
import fortress.modelfind._
import fortress.msfol._
import org.scalatest._

class TptpParserTest extends UnitSuite {

    test("abelian example") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("abelian.p").getFile)
        val fileStream = new FileInputStream(file)
        
        val resultTheory = (new TptpFofParser).parse(fileStream)
        val universeSort = Sort.mkSortConst("_UNIV")
        
        val A = Var("A")
        val B = Var("B")
        val C = Var("C")
        val e = Var("e")
        val f = FuncDecl.mkFuncDecl("f", universeSort, universeSort, universeSort)
        
        val associative = Forall(Seq(A.of(universeSort), B.of(universeSort), C.of(universeSort)),
            Eq(
                App("f", App("f", A, B), C),
                App("f", A, App("f", B, C))))
        
        val identity = Forall(A.of(universeSort),
            And(
                Eq(App("f", A, e), A),
                Eq(App("f", e, A), A)))
        
        val inverse = Forall(A.of(universeSort), Exists(B.of(universeSort), 
            And(
                Eq(App("f", A, B), e),
                Eq(App("f", B, A), e))))
        
        val notAbelian = Not(Forall(Seq(A.of(universeSort), B.of(universeSort)),
            Eq(App("f", A, B), App("f", B, A))))
        
        val expectedTheory = Theory.empty
            .withSort(universeSort)
            .withConstant(e.of(universeSort))
            .withFunctionDeclaration(f)
            .withAxiom(associative)
            .withAxiom(identity)
            .withAxiom(inverse)
            .withAxiom(notAbelian)
        
        resultTheory should be (expectedTheory)
    }
}
