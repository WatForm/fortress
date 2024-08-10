import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations.SmtlibConverter
import fortress.interpretation.EvaluationBasedInterpretation
import fortress.operations.SmtlibTCConverter

class  SmtlibConversionTests extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val f = FuncDecl.mkFuncDecl("f", A, B)
    val P = FuncDecl.mkFuncDecl("P", A, B, Sort.Bool)
    val q = Var("q")
    val r = Var("r")
    val _1A = DomainElement(1, A).asEnumValue
    val _2A = DomainElement(2, A).asEnumValue
    
    test("basic conversion") {
        val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
        val formula2 = ((q ==> r) and (r ==> q)) or (Not(r) <==> q)
        val formula3 = Exists(x of A, Forall(y of B, Distinct(x, x) or App("P", x, y)))
        val formula4 = And(Top, Bottom, q, r)
        
        formula1.smtlib should be ("(forall ((|x| |A|) (|y| |B|)) (= (|f| |x|) |y|))")
        formula2.smtlib should be ("(or (and (=> |q| |r|) (=> |r| |q|)) (= (not |r|) |q|))")
        formula3.smtlib should be ("(exists ((|x| |A|)) (forall ((|y| |B|)) (or (distinct |x| |x|) (|P| |x| |y|))))")
        formula4.smtlib should be ("(and true false |q| |r|)")
    }
    
    test("basic assertion") {
         val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
         formula1.smtlibAssertion should be ("(assert (forall ((|x| |A|) (|y| |B|)) (= (|f| |x|) |y|)))\n")
    }
    
    test("integer conversion") {
        val l = Var("l")
        val u = Var("u")
        val prime = Var("prime")
        
        val formula = Not(Exists(Seq(x of IntSort, y of IntSort), And(
            BuiltinApp(IntGT, x, IntegerLiteral(1)),
            BuiltinApp(IntGT, y, IntegerLiteral(1)),
            BuiltinApp(IntMult, x, y) === prime
        )))
        
        formula.smtlibAssertion should be ("(assert (not (exists ((|x| Int) (|y| Int)) (and (> |x| 1) (> |y| 1) (= (* |x| |y|) |prime|)))))\n")
    }

    test("basic theory") {
        val theory = Theory.empty
                    .withSorts(A, B)
                    .withFunctionDeclarations(f, P)
                    .withConstantDeclarations(x of A, y of B)
                    .withEnumSort(A, _1A, _2A)
                    .withAxiom(App("P", Seq(x,y)))

        theory.smtlib should be ("(declare-sort |B| 0)" + '\n' +
                                "(declare-datatype |A| ( ( |_@1A| )( |_@2A| ) ))" + '\n' +
                                "(declare-fun |f| (|A|) |B|)" + '\n' +
                                "(declare-fun |P| (|A| |B|) Bool)" + '\n' +
                                "(declare-const |x| |A|)" + '\n' +
                                "(declare-const |y| |B|)" + '\n' +
                                "(assert (|P| |x| |y|))" + '\n')
    }
    
    test("basic sorts") {
        val sorts = Seq(IntSort, BoolSort, BitVectorSort(8), A, B)
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        converter.writeSorts(sorts)
        writer.toString should be ("Int Bool (_ BitVec 8) |A| |B|")
    }
    
    test("single sort") {
        val sorts = Seq(IntSort)
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        converter.writeSorts(sorts)
        writer.toString should be ("Int")
    }
    
    test("no sorts") {
        val sorts = Seq()
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        converter.writeSorts(sorts)
        writer.toString should be ("")
    }
    
    test("sort declarations") {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        
        converter.writeSortDecl(IntSort)
        writer.toString should be ("")
        
        converter.writeSortDecl(BoolSort)
        writer.toString should be ("")
        
        converter.writeSortDecl(BitVectorSort(8))
        writer.toString should be ("")
        
        converter.writeSortDecl(A)
        writer.toString should be ("(declare-sort |A| 0)\n")
    }

    test("enum constants declarations") {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)

        converter.writeEnumConst(A, Seq(_1A, _2A))
        writer.toString should be ("(declare-datatype |A| ( ( |_@1A| )( |_@2A| ) ))\n")
    }

    test("function definition1") {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)

        converter.writeFunctionDefinition(
            FunctionDefinition(
                "max",
                List(AnnotatedVar(Var("x"), IntSort), AnnotatedVar(Var("y"), IntSort)),
                IntSort,
                IfThenElse(BuiltinApp(IntLT, Var("x"), Var("y")), Var("y"), Var("x"))
            )
        )

        //println(writer.toString)

        writer.toString should be ("(define-fun |max| ((|x| Int) (|y| Int) ) Int (ite (< |x| |y|) |y| |x|))\n")
    }

    test("function definition2") {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)

        converter.writeFunctionDefinition(
            FunctionDefinition(
                "power2",
                List(AnnotatedVar(Var("x"), IntSort)),
                BoolSort,
                OrList(Eq(Var("x"), IntegerLiteral(8)), Eq(Var("x"), IntegerLiteral(4)), Eq(Var("x"), IntegerLiteral(2)), Eq(Var("x"), IntegerLiteral(1)))
            )
        )

        writer.toString should be("(define-fun |power2| ((|x| Int) ) Bool (or (= |x| 8) (= |x| 4) (= |x| 2) (= |x| 1)))\n")
    }

    test("constant definition"){
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)

        converter.writeConstDefn(
            ConstantDefinition(
                x of IntSort,
                IntegerLiteral(5)
            )
        )

        writer.toString should be ("(define-fun |x| () Int 5)\n")
    }

    test ("bitvector concat") {
        val formula = BuiltinApp(BvConcat, BitVectorLiteral(0, 4), x)
        formula.smtlib should be ("(concat (_ bv0 4) |x|)")
    }

    test ("Ordered Definitions") {
        // expected print order
        val cx = ConstantDefinition(x of BoolSort, Top)
        val fA = FunctionDefinition("fA", Seq(y of BoolSort), BoolSort, Or(x, y))
        val fB = FunctionDefinition("fB", Seq(z of BoolSort), BoolSort, App("fA", z))
        val cz = ConstantDefinition(z of BoolSort, App("fB", Seq(x)))

        // We do this to skip validity checks
        val sig = Signature.empty.copy(constantDefinitions = Set(cz, cx), functionDefinitions = Set(fB, fA))

        val writer = new java.io.StringWriter()
        val converter = new SmtlibConverter(writer)

        converter.writeConstDefn(cx)
        converter.writeFunctionDefinition(fA)
        converter.writeFunctionDefinition(fB)
        converter.writeConstDefn(cz)


        val expected: String = writer.toString()

        val writer2 = new java.io.StringWriter()
        val converter2 = new SmtlibConverter(writer2)
        converter2.writeSignature(sig)
        val result = writer2.toString()
        result should be (expected)

    }

    test ("smtlibtc domain element") {
        val writer = new java.io.StringWriter()
        val converter = new SmtlibTCConverter(writer)

        converter.write(DomainElement(2, SortConst("TestSort")))

        val result = writer.toString()
        val expected = "_@2TestSort"

        result should be (expected)

    }
}
