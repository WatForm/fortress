import java.io.{File, FileInputStream}
import fortress.inputs._
import fortress.modelfinders._
import fortress.msfol._
import fortress.problemstate.{ExactScope, NonExactScope}
import org.scalatest._

import scala.jdk.CollectionConverters._
import scala.jdk.OptionConverters._
import scala.util.Using

class SmtLibParserTest extends UnitSuite {
    
    test("parser throws on error") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("badParse.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        an [fortress.inputs.ParserException] should be thrownBy {parser.parse(fileStream)}
    }
    
    // this .smt2 file has a hidden delete character in it
    // it will generate a line 1:0 lexing error in
    // the test outputs!
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
        val resultTheory = parser.parse(fileStream).getOrElse(null)
        val info: Map[String, String] = parser.getInfo.asScala.toMap
        val logic: Option[String] = parser.getLogic.toScala
        
        logic should be (Some("UF"))

        val source = "\nThis is just a test really.\n"



        info should be (Map(
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
        expectedTheory = expectedTheory.withConstantDeclaration(x.of(A))
        expectedTheory = expectedTheory.withConstantDeclaration(y.of(B))
        
        val p = FuncDecl.mkFuncDecl("p", A, B, Sort.Bool)
        expectedTheory = expectedTheory.withFunctionDeclaration(p)
        
        expectedTheory = expectedTheory.withAxiom(App("p", x, y))
        
        expectedTheory = expectedTheory.withAxiom(Forall(Seq(x.of(A), y.of(B)), Top))
        
        expectedTheory = expectedTheory.withAxiom(Exists(x.of(A), Top))
        
        val q = Var("q")
        expectedTheory = expectedTheory.withConstantDeclaration(q.of(Sort.Bool))
        
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
        expectedTheory = expectedTheory.withConstantDeclaration(a.of(A))
        expectedTheory = expectedTheory.withConstantDeclaration(b.of(A))
        expectedTheory = expectedTheory.withConstantDeclaration(c.of(A))
        
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
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstantDeclaration(x.of(A))
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
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("x")
        expectedTheory = expectedTheory.withConstantDeclaration(x.of(A))
        val f = FuncDecl.mkFuncDecl("f", A, A, A)
        expectedTheory = expectedTheory.withFunctionDeclaration(f)
        val sf = App("f", x, x)
        expectedTheory =
            expectedTheory.withAxiom(Eq(IfThenElse(Eq(sf,x),x,sf),x))
        resultTheory should be (expectedTheory)
    }

    test("sample 2") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("sample2.smt2").getFile)
        val fileStream = new FileInputStream(file)
        
        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)
        val info: Map[String, String] = parser.getInfo.asScala.toMap
        val logic: Option[String] = parser.getLogic.toScala
        
        logic should be (Some("UF"))
        
        val source = "\nTesting $ at beginning of constant/function names.\n"

        info should be (Map(
            "smt-lib-version" -> "2.6",
            "source" -> source,
            "category" -> "toyExample",
            "status" -> "sat",
        ))
        
        var expectedTheory = Theory.empty
        
        val A = Sort.mkSortConst("A")
        expectedTheory = expectedTheory.withSort(A)
        
        val x = Var("$x")
        expectedTheory = expectedTheory.withConstantDeclaration(x.of(A))
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
        val resultTheory = parser.parse(fileStream).getOrElse(null)
        
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
        val resultTheory = parser.parse(fileStream).getOrElse(null)



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
        val resultTheory = parser.parse(fileStream).getOrElse(null)


        Using.resource(new StandardModelFinder()) { mf => {
            mf.setTheory(resultTheory)
            val res = mf.checkSat(false)

            res should be (ModelFinderResult.Sat)
        }}
    }

    test("bitvector parse 1") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("bv1.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        val bv5 = BitVectorSort(5)

        val expected = Theory.empty
            .withSort(bv5)
            .withConstantDeclaration((Var("x")).of(bv5))
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

        Using.resource(new StandardModelFinder()) { mf => {
            mf.setTheory(resultTheory)
            val res = mf.checkSat(false)

            res should be (ModelFinderResult.Sat)
        }}
    }

    test("bitvector parse 2"){
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("bv2.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        val bv4 = BitVectorSort(4)
        val bv3 = BitVectorSort(3)

        val expected = Theory.empty
            .withConstantDefinition(ConstantDefinition(Var("a") of bv3, BitVectorLiteral(-1, 3)))
            .withConstantDefinition(ConstantDefinition(Var("b") of bv3, BitVectorLiteral(-4, 3)))
            .withConstantDefinition(ConstantDefinition(Var("x") of bv4, BitVectorLiteral(-1, 4)))
            // 9 not 8 for -7 not -8
            .withConstantDefinition(ConstantDefinition(Var("y") of bv4, BitVectorLiteral(-7, 4)))

        resultTheory should be (expected)
    }

    test("closure") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("closure1.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser(true)
        val resultTheory = parser.parse(fileStream).getOrElse(null)
        
        val A = SortConst("A")
        val x = Var("x")
        val y = Var("y")

        val expected: Theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A), y.of(A))
            .withFunctionDeclaration(FuncDecl("f", A, A, BoolSort))
            .withAxiom(Closure("f", x, y))

        resultTheory should be (expected)
    }

    test("reflexive-closure") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("reflexive_closure1.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser(true)
        val resultTheory = parser.parse(fileStream).getOrElse(null)
        
        val A = SortConst("A")
        val x = Var("x")
        val y = Var("y")

        val expected: Theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A), y.of(A))
            .withFunctionDeclaration(FuncDecl("f", A, A, BoolSort))
            .withAxiom(ReflexiveClosure("f", x, y))

        resultTheory should be (expected)
    }

    test("scope-info") {
        val classLoader = getClass.getClassLoader
        var parser = new SmtLibParser
        var file = new File(classLoader.getResource("sample_sorts1.smt2").getFile)
        var fileStream = new FileInputStream(file)
        parser.parse(fileStream)

        val A = SortConst("A")
        val B = SortConst("B")
        val CwithParens = SortConst("C()()()")
        var parsedScopes = parser.getScopes()
        parsedScopes should contain (Entry(A, ExactScope(1, true)))
        parsedScopes should contain (Entry(B, ExactScope(2)))


        parser = new SmtLibParser
        file = new File(classLoader.getResource("sample_sorts2.smt2").getFile)
        fileStream = new FileInputStream(file)
        parser.parse(fileStream)
        parsedScopes = parser.getScopes()
        parsedScopes should contain (Entry(A, NonExactScope(1)))
        parsedScopes should contain (Entry(B, NonExactScope(2, true)))

        parser = new SmtLibParser
        file = new File(classLoader.getResource("sample_sorts3.smt2").getFile)
        fileStream = new FileInputStream(file)
        parser.parse(fileStream)
        parsedScopes = parser.getScopes()
        parsedScopes should contain (Entry(A, ExactScope(1, true)))
        parsedScopes should contain (Entry(B, NonExactScope(2, true)))

        parser = new SmtLibParser
        file = new File(classLoader.getResource("sample_sorts4.smt2").getFile)
        fileStream = new FileInputStream(file)
        parser.parse(fileStream)
        parsedScopes = parser.getScopes()
        parsedScopes should contain (Entry(CwithParens, ExactScope(4, true)))
        parsedScopes should contain (Entry(A, ExactScope(1, true)))
        parsedScopes should contain (Entry(B, NonExactScope(2, true)))

    }

    test("scope-info errors"){
        val classLoader = getClass.getClassLoader
        var parser = new SmtLibParser
        var file = new File(classLoader.getResource("sample_sorts_bad.smt2").getFile)
        var fileStream = new FileInputStream(file)
        
        parser.parse(fileStream)
        assertThrows[ParserException](parser.getScopes())
    }

    test("test function definition") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("funcDef.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)


        val fd_max: FunctionDefinition = FunctionDefinition(
            "max",
            List(AnnotatedVar(Var("x"), IntSort), AnnotatedVar(Var("y"), IntSort)),
            IntSort,
            IfThenElse(BuiltinApp(IntLT, Var("x"), Var("y")), Var("y"), Var("x"))
        )

        val fd_power2: FunctionDefinition = FunctionDefinition(
            "power2",
            List(AnnotatedVar(Var("x"), IntSort)),
            BoolSort,
            OrList(Eq(Var("x"), IntegerLiteral(8)), Eq(Var("x"), IntegerLiteral(4)), Eq(Var("x"), IntegerLiteral(2)), Eq(Var("x"), IntegerLiteral(1)))
        )

        resultTheory.functionDefinitions should contain (fd_max)

        resultTheory.functionDefinitions should contain (fd_power2)

    }

    test("quoted-values") {
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("quotedIdentifiers.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        val A = SortConst("A")
        val x = Var("x")
        val mess = Var("!@##")

         val expected: Theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A), mess.of(A))
            .withFunctionDeclaration(FuncDecl("f", A, A))
            .withAxiom(Not(Eq(App("f", x), mess)))
        
        resultTheory should be (expected)

    }
    test("Simple Definitions"){
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("simpleDefns.smt2").getFile)

        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        val x = Var("x")
        
        val expected = Theory.empty
            .withConstantDefinition(ConstantDefinition(x of IntSort, IntegerLiteral(5)))
            .withFunctionDefinition(FunctionDefinition(
                "y", Seq(x of IntSort), IntSort, x 
            ))
            .withConstantDefinition(ConstantDefinition(Var("z") of IntSort, Var("x")))
        resultTheory should be (expected)
    }

    test("domain elements"){
        val classLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("parseDomainElements.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream).getOrElse(null)

        val A = SortConst("A")
        val expected = Theory.empty
            .withSorts(A)
            .withAxiom(Not(Eq(DomainElement(1, A), DomainElement(2, A))))
        resultTheory should be (expected)
    }
}
