import org.scalatest._
import org.junit.Assert._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.modelfind._
import fortress.interpretation._

@RunWith(classOf[JUnitRunner])
class VerifyInterpretationTests extends FunSuite with Matchers {
        val bool: Sort = Sort.Bool

        val w: Var = Var("w")
        val x: Var = Var("x")
        val y: Var = Var("y")
        val z: Var = Var("z")
        val constTrue: Var = Var("constTrue")
        val constFalse: Var = Var("constFalse")

        var booleanTheory: Theory = Theory.empty
                .withConstants(w of bool, x of bool, y of bool, z of bool, constTrue of bool, constFalse of bool)
                .withAxiom(And(w, x, constTrue))
                .withAxiom(Not(Or(y, z, constFalse)))

        val finder: ModelFinder = ModelFinder.createDefault()
        try {
                finder.setTheory(booleanTheory)
                finder.checkSat()
        } catch {
                case e: Throwable => e.printStackTrace()
        }

        val booleanInterpretation: Interpretation = finder.viewModel()

        test("generic test"){
                val t_theory = booleanTheory.withAxiom(x === y)
                val res = t_theory.verifyInterpretation(booleanInterpretation)
                assertFalse(res)
        }
}
