package modelfind

import fortress.modelfind._
import fortress.msfol
import fortress.msfol._
import org.junit.runner.RunWith
import org.scalatest._
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class CountModelTest extends FunSuite with Matchers {
    
    test("basic count") {
        val p = Var("p")
        val q = Var("q")

        // Simple theory, valid interpretations are:
        // p = true, q = false
        // p = false, q = true
        val theory = Theory.empty
            .withConstant(p of BoolSort)
            .withConstant(q of BoolSort)
            .withAxiom(Or(p, q))
            .withAxiom(Not(And(p, q)))

        val finder = ModelFinder.createDefault()
        finder.setTheory(theory)

        finder.checkSat should be (ModelFinderResult.Sat)

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
    }

    test("basic count 2") {
        val p = Var("p")
        val q = Var("q")
        val r = Var("r")

        // Simple theory, valid interpretations are:
        // p = true, q = false
        // p = false, q = true
        val theory = Theory.empty
          .withConstant(p of BoolSort)
          .withConstant(q of BoolSort)
          .withConstant(r of BoolSort)
          .withAxiom(Or(p, q, r))
          .withAxiom(Not(And(p, q, r)))

        val finder = ModelFinder.createDefault()
        finder.countValidModels(theory) should be (6)
    }

    test("function count") {
        val Colour = Sort.mkSortConst("Colour")

        val red = EnumValue("red")
        val yellow = EnumValue("yellow")
        val green = EnumValue("green")

        val next = FuncDecl("next", Colour, Colour)

        val c = Var("c")

        val theory = Theory.empty
          .withEnumSort(Colour, red, yellow, green)
          .withFunctionDeclaration(next)
          .withConstant(c of Colour)
          .withAxiom(Not(App("next", green) === green))
          .withAxiom(Not(App("next", yellow) === yellow))
          .withAxiom(Not(App("next", red) === red))
          .withAxiom(c === App("next", red))

        val finder = ModelFinder.createDefault()
        finder.countValidModels(theory) should be (8)
    }
}

