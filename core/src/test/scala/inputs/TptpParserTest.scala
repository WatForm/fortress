import java.io.{File, FileInputStream, FileOutputStream}
import fortress.inputs._
import fortress.modelfind._
import fortress.msfol._
import org.scalatest._

import java.nio.file.{Files}

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

    test("include example") {
        // Setting up temporary directory for testing file importation
        val tempDir = Files.createTempDirectory("tptp_folder")
        val dest_f = new File(tempDir + "/Problems/ALG/ALG212+1.p")
        dest_f.getParentFile().mkdirs()
        dest_f.createNewFile()
        val classLoader = getClass.getClassLoader
        val src_f = new File(classLoader.getResource("ALG212+1.p").getFile)
        new FileOutputStream(dest_f).getChannel() transferFrom(new FileInputStream(src_f).getChannel(), 0, Long.MaxValue)
        val dest_f2 = new File(tempDir + "/Axioms/ALG002+0.ax")
        dest_f2.getParentFile().mkdirs()
        dest_f2.createNewFile()
        val src_f2 = new File(classLoader.getResource("ALG002+0.ax").getFile)
        new FileOutputStream(dest_f2).getChannel() transferFrom(new FileInputStream(src_f2).getChannel(), 0, Long.MaxValue)
        val resultTheory = (new TptpFofParser).parse(tempDir + "/Problems/ALG/ALG212+1.p")

        val file2 = new File(classLoader.getResource("ALG212+1_imported.p").getFile)
        val fileStream2 = new FileInputStream(file2)
        val expectedTheory = (new TptpFofParser).parse(fileStream2)

        tempDir.toFile().deleteOnExit();
        resultTheory should be(expectedTheory)
    }
}
