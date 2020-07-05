import java.io.{File, FileInputStream}

import fortress.inputs._
import fortress.modelfind._
import fortress.msfol._
import org.scalatest._
import scala.jdk.CollectionConverters._
import scala.jdk.OptionConverters._

class SmtLibParserTest extends UnitSuite {
    
    test("parser throws on error") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("badParse.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        an [fortress.inputs.ParserException] should be thrownBy {parser.parse(fileStream)}
    }
    
    test("lexer throws on error") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("badLexical.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        an [fortress.inputs.LexerException] should be thrownBy {parser.parse(fileStream)}
    }

    test("sample 1") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("sample1.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)
        val info: Map[String, String] = parser.getInfo.asScala.toMap
        val logic: Option[String] = parser.getLogic.toScala
        
        logic should be (Some("UF"))
        
        val source = "\nThis is just a test really.\n"
        
        info should be  (Map(
            "smt-lib-version" -> "2.6",
            "status" -> "sat",
            "category" -> "toyExample",
            "source" -> source
        ))
        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        val B = Sort.mkSortConst("B")
        expectedTheory = expectedTheory.withSort(A)
        expectedTheory = expectedTheory.withSort(B)
        
        val x = Var("x")
        val y = Var("y")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        expectedTheory = expectedTheory.withConstant(y.of(B))
        
        val p = FuncDecl.mkFuncDecl("p", A, B, Sort.Bool)
        expectedTheory = expectedTheory.withFunctionDeclaration(p)
        
        expectedTheory = expectedTheory.withAxiom(App("p", x, y))
        
        expectedTheory = expectedTheory.withAxiom(Forall(Seq(x.of(A), y.of(B)), Top))
        
        expectedTheory = expectedTheory.withAxiom(Exists(x.of(A), Top))
        
        val q = Var("q")
        expectedTheory = expectedTheory.withConstant(q.of(Sort.Bool))
        
        expectedTheory = expectedTheory.withAxiom(Or(q, Not(q)))
        
        expectedTheory = expectedTheory.withAxiom(And(q, q))
        
        expectedTheory = expectedTheory.withAxiom(Not(Bottom))
        
        expectedTheory = expectedTheory.withAxiom(Distinct(q, Bottom))
        
        expectedTheory = expectedTheory.withAxiom(Eq(q, q))
        
        expectedTheory = expectedTheory.withAxiom(Implication(Bottom, Top))
        
        val f = FuncDecl.mkFuncDecl("f", A, A)
        val g = FuncDecl.mkFuncDecl("g", A, A)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        expectedTheory = expectedTheory.withFunctionDeclaration(g)
        
        val a = Var("a")
        val b = Var("b")
        val c = Var("c")
        expectedTheory = expectedTheory.withConstant(a.of(A))
        expectedTheory = expectedTheory.withConstant(b.of(A))
        expectedTheory = expectedTheory.withConstant(c.of(A))
        
        expectedTheory = expectedTheory.withAxiom(
            Forall(x.of(A),
                Eq(
                    App("f",
                        App("g", x)),
                    x)))
        
        resultTheory should be (expectedTheory)
    }

    test("let example") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("let-example.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        val f = FuncDecl.mkFuncDecl("f", A, A, A)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        expectedTheory = expectedTheory.withAxiom(Eq(App("f", x, x),App("f",x,x)))
        resultTheory should be (expectedTheory)
    }


    test("ite example") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("ite-example.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        val f = FuncDecl.mkFuncDecl("f", A, A, A)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        val sf = App("f", x, x)
        expectedTheory = 
            expectedTheory.withAxiom(Eq(IfThenElse(Eq(sf,x),x,sf),x)) 
        resultTheory should be (expectedTheory)
    }

    test("ite returns Bool") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("ite-example2.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        val y = Var("y")
        expectedTheory = expectedTheory.withConstant(y.of(Sort.Bool))
        val f = FuncDecl.mkFuncDecl("f", A, A, Sort.Bool)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        val sf = App("f", x, x)
        expectedTheory = 
            expectedTheory.withAxiom(Or(And(sf,sf),And(Not(sf),y))) 
        resultTheory should be (expectedTheory)
    }

    test("ite returns Bool nested") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("ite-example3.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        val y = Var("y")
        expectedTheory = expectedTheory.withConstant(y.of(Sort.Bool))
        val f = FuncDecl.mkFuncDecl("f", A, A, Sort.Bool)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        val sf = App("f", x, x)
        val ii = Or(And(y,sf),And(Not(y),y))
        expectedTheory = 
            expectedTheory.withAxiom(Or(And(ii,y),And(Not(ii),sf))) 
        resultTheory should be (expectedTheory)
    }

    test("sample 2") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("sample2.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)
        val info: Map[String, String] = parser.getInfo.asScala.toMap
        val logic: Option[String] = parser.getLogic.toScala
        
        logic should be (Some("UF"))
        
        val source = "\nTesting $ at beginning of constant/function names.\n"
        
        info should be  (Map(
            "smt-lib-version" -> "2.6",
            "status" -> "sat",
            "category" -> "toyExample",
            "source" -> source
        ))
        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("$x")
        expectedTheory = expectedTheory.withConstant(x.of(A))
        val p = FuncDecl.mkFuncDecl("$p", A, A, Sort.Bool)
        expectedTheory = expectedTheory.withFunctionDeclaration(p)
        
        expectedTheory = expectedTheory.withAxiom(App("$p", x, x))
        resultTheory should be (expectedTheory)
    }


    test("ramsey coclique k3 bad formulation") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("length-two-paths.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)
        
        val V = Sort.mkSortConst("V")
        val adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool)
        
        val u = Var("u")
        val v = Var("v")
        val x1 = Var("x1")
        val x2 = Var("x2")
        val x3 = Var("x3")
        
        val undirected = Forall(Seq(u.of(V), v.of(V)), Eq(App("adj", u, v), App("adj", v, u)))
        val loopless = Forall(u.of(V), Not(App("adj", u, u)))
        
        val axiom = Not(Exists(Seq(x1.of(V), x2.of(V), x3.of(V)),
            And(
                Distinct(x1, x2, x3),
                Eq(
                    App("adj", x1, x2),
                    App("adj", x2, x3)))))
        
        val expected = Theory.empty
            .withSort(V)
            .withFunctionDeclaration(adj)
            .withAxiom(undirected)
            .withAxiom(loopless)
            .withAxiom(axiom)
        
        resultTheory should be (expected)
    }

    test("integer parse 1") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("integers.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)



        val expected = Theory.empty
                .withAxiom(
                        Eq(
                                Term.mkPlus(
                                        IntegerLiteral(1),
                                        IntegerLiteral(1)),
                                IntegerLiteral(2)))
                .withAxiom(AndList(Seq(
                        Term.mkGE(IntegerLiteral(5), IntegerLiteral(5)),
                        Term.mkGE(IntegerLiteral(5), IntegerLiteral(1))
                )))

        // println("Parsed theory from file:")
        // println(expected)

        resultTheory should be (expected)
    }

    test("integer parse 2") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("integers2.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        val mf = ModelFinder.createDefault
        mf.setTheory(resultTheory)
        val res = mf.checkSat

        res should be (ModelFinderResult.Sat)
    }

    test("bitvector parse 1") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("bv1.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        val bv5 = BitVectorSort(5)

        val expected = Theory.empty
            .withSort(bv5)
            .withConstant((Var("x")).of(bv5))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("f", bv5, bv5, bv5))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("g", bv5, bv5))
            .withAxiom(
                Eq(
                    App(
                        "f",
                        Var("x"),
                        Var("x")),
                    Term.mkBvPlus(
                        Var("x"),
                        Var("x")
                    )))
            .withAxiom(
                Eq(
                    App(
                        "g",
                        Var("x")),
                    Term.mkBvNeg(Var("x"))))
            .withAxiom(
                Eq(
                    App("f",
                        App("g",
                            Var("x")),
                        Var("x")),
                    BitVectorLiteral(0, 5)
                ))

        resultTheory should be (expected)

        val mf = ModelFinder.createDefault
        mf.setTheory(resultTheory)
        val res = mf.checkSat

        res should be (ModelFinderResult.Sat)
    }
}
