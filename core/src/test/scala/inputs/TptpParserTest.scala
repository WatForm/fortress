import java.io.{ByteArrayInputStream, File, FileInputStream, FileOutputStream, StringBufferInputStream}
import fortress.inputs._
import fortress.modelfind._
import fortress.msfol._
import org.scalatest._

import java.nio.file.Files
import scala.reflect.io.Directory

class TptpParserTest extends UnitSuite {

    def createFileInTempDir(src: File, dest: File): Unit = {
        dest.getParentFile().mkdirs()
        dest.createNewFile()
        new FileOutputStream(dest).getChannel() transferFrom(new FileInputStream(src).getChannel(), 0, Long.MaxValue)
    }

    test("abelian example") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("abelian.p").getFile)
        val fileStream = new FileInputStream(file)

        val resultTheory = (new TptpFofParser).parse(fileStream).getOrElse()
        val universeSort = Sort.mkSortConst("_UNIV")

        val A = Var("Aaa")
        val B = Var("Baa")
        val C = Var("Caa")
        val e = Var("eaa")
        val f = FuncDecl.mkFuncDecl("faa", universeSort, universeSort, universeSort)

        val associative = Forall(Seq(A.of(universeSort), B.of(universeSort), C.of(universeSort)),
            Eq(
                App("faa", App("faa", A, B), C),
                App("faa", A, App("faa", B, C))))

        val identity = Forall(A.of(universeSort),
            And(
                Eq(App("faa", A, e), A),
                Eq(App("faa", e, A), A)))

        val inverse = Forall(A.of(universeSort), Exists(B.of(universeSort),
            And(
                Eq(App("faa", A, B), e),
                Eq(App("faa", B, A), e))))

        val notAbelian = Not(Forall(Seq(A.of(universeSort), B.of(universeSort)),
            Eq(App("faa", A, B), App("faa", B, A))))

        val expectedTheory = Theory.empty
          .withSort(universeSort)
          .withConstant(e.of(universeSort))
          .withFunctionDeclaration(f)
          .withAxiom(associative)
          .withAxiom(identity)
          .withAxiom(inverse)
          .withAxiom(notAbelian)

        resultTheory should be(expectedTheory)
    }

    test("include example ALG212") {
        // Setting up temporary directory for testing file importation
        val tempDir = Files.createTempDirectory("tptp_folder")
        val classLoader = getClass.getClassLoader
        val src1 = new File(classLoader.getResource("ALG212+1.p").getFile)
        val dest1 = new File(tempDir + "/Problems/ALG/ALG212+1.p")
        createFileInTempDir(src1, dest1)
        val src2 = new File(classLoader.getResource("ALG002+0.ax").getFile)
        val dest2 = new File(tempDir + "/Axioms/ALG002+0.ax")
        createFileInTempDir(src2, dest2)
        val resultTheory = (new TptpFofParser).parse(tempDir + "/Problems/ALG/ALG212+1.p").getOrElse()

        // Clean up the temporary directory
        val directory = new Directory(tempDir.toFile)
        directory.deleteRecursively() should be(true)

        val file2 = new File(classLoader.getResource("ALG212+1_imported.p").getFile)
        val fileStream2 = new FileInputStream(file2)
        val expectedTheory = (new TptpFofParser).parse(fileStream2).getOrElse()

        resultTheory should be(expectedTheory)
    }

    test("include example GEO091") {
        // Setting up temporary directory for testing file importation
        val tempDir = Files.createTempDirectory("tptp_folder")
        val classLoader = getClass.getClassLoader
        val src1 = new File(classLoader.getResource("GEO091+1.p").getFile)
        val dest1 = new File(tempDir + "/Problems/GEO/GEO091+1.p")
        createFileInTempDir(src1, dest1)
        val src2 = new File(classLoader.getResource("GEO004+0.ax").getFile)
        val dest2 = new File(tempDir + "/Axioms/GEO004+0.ax")
        createFileInTempDir(src2, dest2)
        val resultTheory = (new TptpFofParser).parse(tempDir + "/Problems/GEO/GEO091+1.p").getOrElse()

        // Clean up the temporary directory
        val directory = new Directory(tempDir.toFile)
        directory.deleteRecursively() should be(true)

        val file2 = new File(classLoader.getResource("GEO091+1_imported.p").getFile)
        val fileStream2 = new FileInputStream(file2)
        val expectedTheory = (new TptpFofParser).parse(fileStream2).getOrElse()

        resultTheory should be(expectedTheory)
    }

    test("include example MED009") {
        // Setting up temporary directory for testing file importation
        val tempDir = Files.createTempDirectory("tptp_folder")
        val classLoader = getClass.getClassLoader
        val src1 = new File(classLoader.getResource("MED009+1.p").getFile)
        val dest1 = new File(tempDir + "/Problems/MED/MED009+1.p")
        createFileInTempDir(src1, dest1)
        val src2 = new File(classLoader.getResource("MED001+0.ax").getFile)
        val dest2 = new File(tempDir + "/Axioms/MED001+0.ax")
        createFileInTempDir(src2, dest2)
        val src3 = new File(classLoader.getResource("MED001+1.ax").getFile)
        val dest3 = new File(tempDir + "/Axioms/MED001+1.ax")
        createFileInTempDir(src3, dest3)
        val resultTheory = (new TptpFofParser).parse(tempDir + "/Problems/MED/MED009+1.p").getOrElse()

        // Clean up the temporary directory
        val directory = new Directory(tempDir.toFile)
        directory.deleteRecursively() should be(true)

        val file2 = new File(classLoader.getResource("MED009+1_imported.p").getFile)
        val fileStream2 = new FileInputStream(file2)
        val expectedTheory = (new TptpFofParser).parse(fileStream2).getOrElse()

        resultTheory should be(expectedTheory)
    }

    test("defined proposition example") {
        val tptp_content = "fof('defined-prop',axiom,( " +
          "( a = a => $true ) & " +
          "( $false  => a = a))" +
          ")."
        val inputStream = new ByteArrayInputStream(tptp_content.getBytes())

        val resultTheory = (new TptpFofParser).parse(inputStream).getOrElse()
        val universeSort = Sort.mkSortConst("_UNIV")

        val a = Var("a" + "aa")
        val axiom1 = And(Implication(Eq(a, a), Top), Implication(Bottom, Eq(a, a)))

        val expectedTheory = Theory.empty
          .withSort(universeSort)
          .withConstant(a.of(universeSort))
          .withAxiom(axiom1)

        resultTheory should be(expectedTheory)
    }

}
