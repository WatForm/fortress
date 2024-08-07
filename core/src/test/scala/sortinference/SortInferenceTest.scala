import org.scalatest._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.msfol.Sort.BitVector

class SortInferenceTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    val C = Sort.mkSortConst("C")
    val D = Sort.mkSortConst("D")
    
    val _0 = Sort.mkSortConst("S0")
    val _1 = Sort.mkSortConst("S1")
    val _2 = Sort.mkSortConst("S2")
    val _3 = Sort.mkSortConst("S3")
    val _4 = Sort.mkSortConst("S4")
    
    test("function, no axioms") {
        val f = FuncDecl("f", A, A, A)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)

        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, no axioms") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)

        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do not restrict sorts") {
        val f = FuncDecl("f", A, A, A)
        val r = Var("r")
        val r1 = Var("r1")
        val r2 = Var("r2")
        val c = Var("c")
        val c1 = Var("c1")
        val c2 = Var("c2")
        
        val rowConstraint = Forall(Seq(r of A, c1 of A, c2 of A),
            (App("f", r, c1) === App("f", r, c2)) ==> (c1 === c2))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(rowConstraint)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)

        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do not restrict sorts") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val ax = Forall(x of A, Exists(Seq(y of A, z of A), App("P", x, y, z)))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)

        substitution(generalTheory) should be (theory)
    }
    
    test("function, axioms that do restrict sorts") {
        val f = FuncDecl("f", A, A, A)
        val x = Var("x")
        val y = Var("y")
        
        // Force 1st input = output
        val ax = Forall(Seq(x of A, y of A), App("f", x, y) === y)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(ax)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)

        substitution(generalTheory) should be (theory)
    }
    
    test("predicate, axioms that do restrict sorts") {
        val P = FuncDecl("P", A, A, A, Sort.Bool)
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        // Force 1st input = 3rd input
        val ax = Forall(x of A, Not(Exists(y of A, App("P", x, y, x))))
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
            .withAxiom(ax)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)

        substitution(generalTheory) should be (theory)
    }
    
    test("when theory is already maximally general, return original theory") {
        val f = FuncDecl("f", A, A, A)
        val x = Var("x")
        
        val ax = Forall(x of A, App("f", x, x) === x)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(ax)
            
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory should be (theory)
        substitution shouldBe Symbol("isIdentity")
    }

    test("if-then-else") {
        pending
    }

    test("closures") {
        pending
    }

    test("function definitions 1") {
        val x = Var("x")
        val y = Var("y")
        // g : A * A -> A
        val g = FuncDecl("g", A, A, A)
        // f: A * A -> A
        // f(x, y) = g(x, g(x, y))
        val f = FunctionDefinition("f", Seq(x of A, y of A), A, App("g", x, App("g", x, y)))

        // Result should be as in
        // g: A * B -> B
        // f: A * B -> B

        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(g)
            .withFunctionDefinitions(f)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        val gGeneral = generalTheory.functionDeclarations.find(_.name == "g").get
        val fGeneral = generalTheory.functionDefinitions.find(_.name == "f").get
        val g0 = gGeneral.argSorts(0)
        val g1 = gGeneral.argSorts(1)
        val gout = gGeneral.resultSort
        val f0 = fGeneral.argSorts(0)
        val f1 = fGeneral.argSorts(1)
        val fout = fGeneral.resultSort
        g0 should not be (g1)
        g1 should be (gout)
        f0 should be (g0)
        f1 should be (g1)
        fout should be (gout)

        substitution(generalTheory) should be (theory)
    }

    test("function definitions 2") {
        val x = Var("x")
        val y = Var("y")
        // g : A * A -> A
        val g = FuncDecl("g", A, A, A)
        val h = FuncDecl("h", A, A, A)
        // f: A * A -> A
        // f(x, y) = h(g(x, y), x)
        val f = FunctionDefinition("f", Seq(x of A, y of A), A, App("h", App("g", x, y), x))

        // Result should be as in
        // g: A * B -> C
        // h: C * A -> D
        // f: A * B -> D

        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(g, h)
            .withFunctionDefinitions(f)
        
        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (4)
        val gGeneral = generalTheory.functionDeclarations.find(_.name == "g").get
        val hGeneral = generalTheory.functionDeclarations.find(_.name == "h").get
        val fGeneral = generalTheory.functionDefinitions.find(_.name == "f").get
        val g0 = gGeneral.argSorts(0)
        val g1 = gGeneral.argSorts(1)
        val gout = gGeneral.resultSort
        val h0 = hGeneral.argSorts(0)
        val h1 = hGeneral.argSorts(1)
        val h2 = hGeneral.resultSort
        val f0 = fGeneral.argSorts(0)
        val f1 = fGeneral.argSorts(1)
        val f2 = fGeneral.resultSort
        Set(g0, g1, gout, h2).size should be (4)
        Set(g0, h1, f0).size should be (1) // A
        Set(g1, f1).size should be (1) // B
        Set(gout, h0).size should be (1) // C
        Set(h2, f2).size should be (1)

        substitution(generalTheory) should be (theory)
    }

    test("constant definitions") {
        val c1 = Var("c1")
        val c2 = Var("c2")
        val c3 = Var("c3")
        val f = FuncDecl("f", A, A, A)
        val c4 = Var("c4")
        val c4Defn = ConstantDefinition(c4 of A, App("f", c1, c2))
        val ax = Eq(c3, c4)

        // Result should be
        // c1: A, c2: B, c3: C, c4: C, f: A x B -> C
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclaration(f)
            .withConstantDeclarations(c1 of A, c2 of A, c3 of A)
            .withConstantDefinition(c4Defn)

        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (3)
        val c1General = generalTheory.constantDeclarations.find(_.name == "c1").get
        val c2General = generalTheory.constantDeclarations.find(_.name == "c2").get
        val c3General = generalTheory.constantDeclarations.find(_.name == "c3").get
        val c4General = generalTheory.constantDefinitions.find(_.avar.name == "c4").get
        Set(c1General.sort, c2General.sort, c3General.sort).size should be (3)
        c3General.sort should be (c4General.avar.sort)

        substitution(generalTheory) should be (theory)
    }

    test("enum values: conservative approach") {
        val c = Var("c")
        val e1 = EnumValue("e1")
        val e2 = EnumValue("e2")
        val e3 = EnumValue("e3")

        val f = FuncDecl("f", A, A, A, A)

        val ax = Eq(App("f", e1, e2, c), c)

        // The conservative solution to this requires that e1, e2, e3 all have the same sort, even though nothing in this axiom suggests as such.
        // f: A x A x B -> B
        val theory = Theory.empty
            .withEnumSort(A, e1, e2, e3)
            .withConstantDeclaration(c of A)
            .withFunctionDeclaration(f)
            .withAxiom(ax)

        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        val fGeneral = generalTheory.functionDeclarations.find(_.name == "f").get
        val f0 = fGeneral.argSorts(0)
        val f1 = fGeneral.argSorts(1)
        val f2 = fGeneral.argSorts(2)
        val fout = fGeneral.resultSort
        f0 should be (f1)
        f1 should not be (f2)
        f2 should be (fout)
        theory.enumConstants.size should be (1)
        val (generalSort, generalEnumVals) = theory.enumConstants.head
        generalEnumVals.size should be (3)
        generalTheory.constantDeclarations.size should be (1)
        generalTheory.constantDeclarations.find(_.name == "c").get.sort should not be (generalSort)
        
        substitution(generalTheory) should be (theory)
    }

    test("booleans should play no role in sort inference") {
        val c1 = Var("c1")
        val c2 = Var("c2")
        val f = FuncDecl("f", A, BoolSort, A)
        val p = FuncDecl("p", A, BoolSort)
        val q = FuncDecl("q", BoolSort, BoolSort)

        val ax1 = App("q", App("p", App("f", c1, c2)))

        val theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(c1 of A, c2 of BoolSort)
            .withFunctionDeclarations(f, p, q)
            .withAxiom(ax1)

        // Result should be
        // c1: A, c2: Bool, f: A x Bool -> B, p: B -> Bool, q: Bool -> Bool

        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        val c1General = generalTheory.constantDeclarations.find(_.name == "c1").get
        val c2General = generalTheory.constantDeclarations.find(_.name == "c2").get
        val fGeneral = generalTheory.functionDeclarations.find(_.name == "f").get
        val pGeneral = generalTheory.functionDeclarations.find(_.name == "p").get
        val qGeneral = generalTheory.functionDeclarations.find(_.name == "q").get
        val c1Sort = c1General.sort
        val c2Sort = c2General.sort
        val f0 = fGeneral.argSorts(0)
        val f1 = fGeneral.argSorts(1)
        val fout = fGeneral.resultSort
        val p0 = pGeneral.argSorts(0)
        val pout = pGeneral.resultSort
        val q0 = qGeneral.argSorts(0)
        val qout = qGeneral.resultSort
        c1Sort should not be (BoolSort)
        c2Sort should be (BoolSort)
        f0 should be (c1Sort)
        f1 should be (BoolSort)
        fout should not be (BoolSort)
        fout should not be (f0)
        p0 should be (fout)
        pout should be (BoolSort)
        q0 should be (BoolSort)
        qout should be (BoolSort)

        substitution(generalTheory) should be (theory)
    }

    test("integers should play no role in sort inference") {
        val c1 = Var("c1")
        val c2 = Var("c2")
        val c3 = Var("c3")
        val gInt = FuncDecl("gInt", A, IntSort)
        val fInt = FuncDecl("fInt", A, IntSort, A)

        val ax1 = Eq(App("gInt", c1), IntegerLiteral(4))
        val ax2 = Eq(BuiltinApp(IntPlus, App("gInt", App("fInt", c2, c3)), IntegerLiteral(0)), IntegerLiteral(4))
        val theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(c1 of A, c2 of A, c3 of IntSort)
            .withFunctionDeclarations(gInt, fInt)
            .withAxioms(Seq(ax1, ax2))

        // Result should be
        // c1: A, c2: B, c3: Int
        // gInt: A -> Int
        // fInt: B x Int -> A

        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        val c1General = generalTheory.constantDeclarations.find(_.name == "c1").get
        val c2General = generalTheory.constantDeclarations.find(_.name == "c2").get
        val c3General = generalTheory.constantDeclarations.find(_.name == "c3").get
        val gGeneral = generalTheory.functionDeclarations.find(_.name == "gInt").get
        val fGeneral = generalTheory.functionDeclarations.find(_.name == "fInt").get
        Set(c1General.sort, c2General.sort, IntSort).size should be (3)
        c3General.sort should be (IntSort)
        gGeneral.argSorts(0) should be (c1General.sort)
        gGeneral.resultSort should be (IntSort)
        fGeneral.argSorts(0) should be (c2General.sort)
        fGeneral.argSorts(1) should be (IntSort)
        fGeneral.resultSort should be (c1General.sort)
        
        substitution(generalTheory) should be (theory)
    }

    test("bitvectors should play no role in sort inference") {
        val c4 = Var("c4")
        val c5 = Var("c5")
        val c6 = Var("c6")
        val gBV = FuncDecl("gBV", A, BitVector(8))
        val fBV = FuncDecl("fBV", A, BitVector(8), A)

        val ax3 = Eq(App("gBV", c4), BitVectorLiteral(4, 8))
        val ax4 = Eq(BuiltinApp(BvPlus, App("gBV", App("fBV", c5, c6)), BitVectorLiteral(0, 8)), BitVectorLiteral(4, 8))

        val theory = Theory.empty
            .withSorts(A)
            .withConstantDeclarations(c4 of A, c5 of A, c6 of BitVector(8))
            .withFunctionDeclarations(gBV, fBV)
            .withAxioms(Seq(ax3, ax4))

        // Result should be
        // c4: A, c5: B, c6: BV(8)
        // gBV: A -> BV(8)
        // fBV: B x BV(8) -> A

        val (generalTheory, substitution) = theory.inferSorts
        generalTheory.sorts.size should be (2)
        val c4General = generalTheory.constantDeclarations.find(_.name == "c4").get
        val c5General = generalTheory.constantDeclarations.find(_.name == "c5").get
        val c6General = generalTheory.constantDeclarations.find(_.name == "c6").get
        val gGeneral = generalTheory.functionDeclarations.find(_.name == "gBV").get
        val fGeneral = generalTheory.functionDeclarations.find(_.name == "fBV").get
        Set(c4General.sort, c5General.sort, BitVector(8)).size should be (3)
        c6General.sort should be (BitVector(8))
        gGeneral.argSorts(0) should be (c4General.sort)
        gGeneral.resultSort should be (BitVectorSort(8))
        fGeneral.argSorts(0) should be (c5General.sort)
        fGeneral.argSorts(1) should be (BitVectorSort(8))
        fGeneral.resultSort should be (c4General.sort)

        substitution(generalTheory) should be (theory)
    }
}
