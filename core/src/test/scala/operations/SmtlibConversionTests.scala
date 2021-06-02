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
    
    test("basic conversion") {
        val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
        val formula2 = ((q ==> r) and (r ==> q)) or (Not(r) <==> q)
        val formula3 = Exists(x of A, Forall(y of B, Distinct(x, x) or App("P", x, y)))
        val formula4 = And(Top, Bottom, q, r)
        
        formula1.smtlib should be ("(forall ((x A) (y B)) (= (f x) y))")
        formula2.smtlib should be ("(or (and (=> q r) (=> r q)) (= (not r) q))")
        formula3.smtlib should be ("(exists ((x A)) (forall ((y B)) (or (distinct x x) (P x y))))")
        formula4.smtlib should be ("(and true false q r)")
    }
    
    test("basic assertion") {
         val formula1 = Forall(Seq(x of A, y of B), App("f", x) === y)
         formula1.smtlibAssertion should be ("(assert (forall ((x A) (y B)) (= (f x) y)))")
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
        
        formula.smtlibAssertion should be ("(assert (not (exists ((x Int) (y Int)) (and (> x 1) (> y 1) (= (* x y) prime)))))")
    }

    test("basic theory") {
        val theory = Theory.empty
                    .withSorts(A, B)
                    .withFunctionDeclarations(f, P)
                    .withConstants(x of A, y of B)
                    .withAxiom(App("P", Seq(x,y)))

        theory.smtlib should be ("(declare-sort A 0)" +
                                "(declare-sort B 0)" +
                                "(declare-fun f (A) B)" +
                                "(declare-fun P (A B) Bool)" +
                                "(declare-const x A)" +
                                "(declare-const y B)" +
                                "(assert (P x y))")
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
}