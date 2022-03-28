import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations.SmtlibConverter

class SmtlibConversionTests extends UnitSuite {
    
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
        
        formula1.smtlib should be ("(forall ((xaa A) (yaa B)) (= (faa xaa) yaa))")
        formula2.smtlib should be ("(or (and (=> qaa raa) (=> raa qaa)) (= (not raa) qaa))")
        formula3.smtlib should be ("(exists ((xaa A)) (forall ((yaa B)) (or (distinct xaa xaa) (Paa xaa yaa))))")
        formula4.smtlib should be ("(and true false qaa raa)")
    }
    
    test("basic assertion") {
         val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
         formula1.smtlibAssertion should be ("(assert (forall ((xaa A) (yaa B)) (= (faa xaa) yaa)))")
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
        
        formula.smtlibAssertion should be ("(assert (not (exists ((xaa Int) (yaa Int)) (and (> xaa 1) (> yaa 1) (= (* xaa yaa) primeaa)))))")
    }

    test("basic theory") {
        val theory = Theory.empty
                    .withSorts(A, B)
                    .withFunctionDeclarations(f, P)
                    .withConstants(x of A, y of B)
                    .withEnumSort(A, _1A, _2A)
                    .withAxiom(App("P", Seq(x,y)))

        theory.smtlib should be ("(declare-sort B 0)" +
                                "(declare-datatypes () ((A _@1Aaa _@2Aaa)))" +
                                "(declare-fun faa (A) B)" +
                                "(declare-fun Paa (A B) Bool)" +
                                "(declare-const xaa A)" +
                                "(declare-const yaa B)" +
                                "(assert (Paa xaa yaa))")
    }
    
    test("basic sorts") {
        val sorts = Seq(IntSort, BoolSort, BitVectorSort(8), A, B)
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        converter.writeSorts(sorts)
        writer.toString should be ("Int Bool (_ BitVec 8) A B")
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
        writer.toString should be ("(declare-sort A 0)")
    }

    test("enum constants declarations") {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)

        converter.writeEnumConst(A, Seq(_1A, _2A))
        writer.toString should be ("(declare-datatypes () ((A _@1Aaa _@2Aaa)))")
    }
}
