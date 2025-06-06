import fortress.modelfinders._
import fortress.msfol._
import org.scalatest._
import scala.util.Using

class CountModelTest extends UnitSuite {
    
    test("basic count") {
        // pending
        val p = Var("p")
        val q = Var("q")

        // Simple theory, valid interpretations are:
        // p = true, q = false
        // p = false, q = true
        val theory = Theory.empty
            .withConstantDeclaration(p of BoolSort)
            .withConstantDeclaration(q of BoolSort)
            .withAxiom(Or(p, q))
            .withAxiom(Not(And(p, q)))

        Using.resource(new JoeZEROModelFinder) { finder => {
            finder.setTheory(theory)

            finder.checkSat(false) should be (ModelFinderResult.Sat)

            var model = finder.viewModel()
            val pVal1 = model.constantInterpretations(p of BoolSort)
            val qVal1 = model.constantInterpretations(q of BoolSort)

            finder.nextInterpretation() should be (ModelFinderResult.Sat)
            model = finder.viewModel()

            val pVal2 = model.constantInterpretations(p of BoolSort)
            val qVal2 = model.constantInterpretations(q of BoolSort)

            // Check that the second interpretation is the opposite of the first
            assert(pVal1 != qVal1)
            assert(pVal1 != pVal2)
            assert(qVal1 != qVal2)
            finder.nextInterpretation() should be (ModelFinderResult.Unsat)

            finder.countValidModels(theory) should be (2)
        }}
    }

    test("basic count 2") {
        // pending
        val p = Var("p")
        val q = Var("q")
        val r = Var("r")

        // Simple theory, valid interpretations are:
        val theory = Theory.empty
          .withConstantDeclaration(p of BoolSort)
          .withConstantDeclaration(q of BoolSort)
          .withConstantDeclaration(r of BoolSort)
          .withAxiom(Or(p, q, r))
          .withAxiom(Not(And(p, q, r)))

        Using.resource(new JoeZEROModelFinder) { finder =>
            finder.countValidModels(theory) should be (6)
        }
    }

    test("function count easy") {
        // pending
        val Colour = Sort.mkSortConst("Colour")

        val red = EnumValue("red")
        val green = EnumValue("green")

        val f = FuncDecl("f", Colour, Colour)

        val c = Var("c")

        val theory = Theory.empty
          .withEnumSort(Colour, red, green)
          .withFunctionDeclaration(f)
          .withConstantDeclaration(c of Colour)
          .withAxiom(Not(App("f", green) === green))
          .withAxiom(c === App("f", red))

        Using.resource(new JoeZEROModelFinder) { finder =>
            finder.countValidModels(theory) should be (2)
        }
    }

    test("function count") {
        // pending
        val Colour = Sort.mkSortConst("Colour")

        val red = EnumValue("red")
        val yellow = EnumValue("yellow")
        val green = EnumValue("green")

        val next = FuncDecl("next", Colour, Colour)

        val c = Var("c")

        val theory = Theory.empty
          .withEnumSort(Colour, red, yellow, green)
          .withFunctionDeclaration(next)
          .withConstantDeclaration(c of Colour)
          .withAxiom(Not(App("next", green) === green))
          .withAxiom(Not(App("next", yellow) === yellow))
          .withAxiom(Not(App("next", red) === red))
          .withAxiom(c === App("next", red))

        Using.resource(new JoeZEROModelFinder) { finder =>
            finder.countValidModels(theory) should be (8)
        }
    }
    
    test("relational bijection count") {
        // pending
        // Create Sorts
        val Row = Sort.mkSortConst("Row") // Rows
        val Col = Sort.mkSortConst("Col") // Columns
        
        // Create declaration for rook assignment predicate
        // Rook: Row x Col -> Bool
        val Rook = FuncDecl("Rook", Row, Col, Sort.Bool)
        
        // Create variables to use in axioms
        val r = Var("r")
        val r1 = Var("r1")
        val r2 = Var("r2")
        val c = Var("c")
        val c1 = Var("c1")
        val c2 = Var("c2")
        
        // Create axioms
        // "Each row has a rook in it"
        val rowConstraint1 = Forall(r.of(Row), Exists(c.of(Col), App("Rook", r, c)))
        // "At most one rook in each row"
        val rowConstraint2 = Forall(List(r.of(Row), c1.of(Col), c2.of(Col)),
            Implication(
                And(App("Rook", r, c1), App("Rook", r, c2)),
                Eq(c1, c2)))
        // "Each column has a rook in it"
        val colConstraint1 = Forall(c.of(Col), Exists(r.of(Row), App("Rook", r, c)))
        // "At most one rook in each column"
        val colConstraint2 = Forall(List(c.of(Col), r1.of(Row), r2.of(Row)),
            Implication(
                And(App("Rook", r1, c), App("Rook", r2, c)),
                Eq(r1, r2)))
        
        // Begin with the empty theory
        val rookTheory =  Theory.empty
        // Add sorts
            .withSorts(Row, Col)
        // Add declarations
            .withFunctionDeclarations(Rook)
        // Add constraints
            .withAxiom(rowConstraint1)
            .withAxiom(rowConstraint2)
            .withAxiom(colConstraint1)
            .withAxiom(colConstraint2)
        
        Using.resource(new JoeZEROModelFinder) { finder => {
            finder.setExactScope(Row, 4)
            finder.setExactScope(Col, 4)
            finder.countValidModels(rookTheory) should be (24)
        }}
    }
    
    test("skolem witnesses not added to count") {
        // pending
        val A = Sort.mkSortConst("A")
        
        val x = Var("x")
        val y = Var("y")
        
        val f = FuncDecl("f", A, A)
        
        val theory = Theory.empty
            .withSorts(A)
            .withFunctionDeclarations(f)
            .withAxiom(Forall(x of A, Exists(y of A, Not(App("f", x) === y))))
        
        Using.resource(new JoeZEROModelFinder) { finder => {
            finder.setExactScope(A, 3)
            finder.countValidModels(theory) should be (27)
        }}
    }
}
