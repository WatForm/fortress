import fortress.inputs.SmtLibSubsetParser.DistinctContext
import org.scalatest._
import org.junit.Assert._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import fortress.msfol._
import fortress.modelfind._
import fortress.interpretation._

@RunWith(classOf[JUnitRunner])
class VerifyInterpretationTests extends FunSuite with Matchers {
        /** Unit tests for Theory.verifyInterpretation()
          *
          * We first create a raw theory with all our constant & function definitions,
          * then apply constraints (axioms) and pass it through Z3 to generate desired
          * values for the constants.
          *
          * We then test by appending individual axioms onto the raw theory and then
          * running it through the verifier to test that axiom with the interpretation we got back.
          */

        def injectAxiomAndTest(theory: Theory, interpretation: Interpretation)(axiom: Term): Boolean = {
                theory.withAxiom(axiom).verifyInterpretation(interpretation)
        }

        val bool: Sort = Sort.Bool

        val true1: Var = Var("true1")
        val true2: Var = Var("true2")
        val true3: Var = Var("true3")
        val false1: Var = Var("false1")
        val false2: Var = Var("false2")
        val false3: Var = Var("false3")

        val rawBooleanTheory : Theory = Theory.empty
                .withConstants(true1 of bool, true2 of bool, false1 of bool,
                        false2 of bool, true3 of bool, false3 of bool)

        val booleanTheory: Theory = rawBooleanTheory
                .withAxiom(And(true1, true2, true3))
                .withAxiom(Not(Or(false1, false2, false3)))

        val booleanFinder: ModelFinder = ModelFinder.createDefault()
        try {
                booleanFinder.setTheory(booleanTheory)
                booleanFinder.checkSat()
        } catch {
                case e: Throwable => e.printStackTrace()
        }

        val booleanInterpretation: Interpretation = booleanFinder.viewModel()
        val booleanTest: Term => Boolean = injectAxiomAndTest(rawBooleanTheory, booleanInterpretation)

        test("boolean true/false/not"){
                assertTrue(booleanTest(true1))
                assertTrue(booleanTest(Not(false1)))
                assertFalse(booleanTest(Not(true1)))
                assertFalse(booleanTest(false1))
        }

        test("boolean and/or"){
                assertTrue(booleanTest(And(true1, true2, true3)))
                assertTrue(booleanTest(Or(true1, false1, false2, false3)))
                assertFalse(booleanTest(And(true1, true2, false1, false2)))
                assertFalse(booleanTest(Or(false3)))
        }

        test("boolean implication/iff/eq"){
                assertTrue(booleanTest(true1 === true2))
                assertTrue(booleanTest(Not(true1) === false1))
                assertTrue(booleanTest(true1 ==> true1))
                assertTrue(booleanTest(false1 ==> true1))
                assertTrue(booleanTest(false1 ==> false1))
                assertTrue(booleanTest(Iff(true1, true2)))
                assertTrue(booleanTest(Iff(false1, false2)))
                assertFalse(booleanTest(true1 === false1))
                assertFalse(booleanTest(true1 ==> false1))
                assertFalse(booleanTest(Iff(true1, false1)))
                assertFalse(booleanTest(Iff(false1, true1)))
        }

        val fruit: Sort = Sort.mkSortConst("fruit")

        val apple: Var = Var("apple")
        val orange: Var = Var("orange")
        val banana: Var = Var("banana")
        val plum: Var = Var("plum")
        val peach: Var = Var("peach")

        val fruitVals: List[EnumValue] = List(
                Term.mkEnumValue("apple"),
                Term.mkEnumValue("orange"),
                Term.mkEnumValue("banana"),
                Term.mkEnumValue("plum"),
                Term.mkEnumValue("peach")
        )

        val identity: FuncDecl = FuncDecl.mkFuncDecl("identity", fruit, fruit)
        val doubleIdentity: FuncDecl = FuncDecl.mkFuncDecl("doubleIdentity", fruit, fruit, fruit)
        val tripleIdentity: FuncDecl = FuncDecl.mkFuncDecl("tripleIdentity", fruit, fruit, fruit, fruit)

        val temp: Var = Var("temp")
        val rawSortTheory: Theory = Theory.empty
                .withEnumSort(fruit, fruitVals)
                .withConstants(apple of fruit, orange of fruit,
                        banana of fruit, plum of fruit, peach of fruit)
                .withFunctionDeclarations(identity, doubleIdentity, tripleIdentity)

        val sortTheory: Theory = rawSortTheory
                .withAxiom(Distinct(apple, orange, banana, plum, peach))
                .withAxiom(Forall(temp of fruit, temp === App("identity", temp)))
                .withAxiom(Forall(temp of fruit, temp === App("doubleIdentity", temp, temp)))
                .withAxiom(Forall(temp of fruit, temp === App("tripleIdentity", temp, temp, temp)))

        val sortFinder: ModelFinder = ModelFinder.createDefault()
        try {
                sortFinder.setTheory(sortTheory)
                sortFinder.checkSat()
        } catch {
                case e: Throwable => e.printStackTrace()
        }

        val sortInterpretation: Interpretation = sortFinder.viewModel()
        val sortTest: Term => Boolean = injectAxiomAndTest(rawSortTheory, sortInterpretation)

        test("sort eq"){
                assertTrue(sortTest(apple === apple))
                assertTrue(sortTest(orange === orange))
                assertTrue(sortTest(plum === plum))
                assertTrue(sortTest(peach === peach))
                assertTrue(sortTest(banana === banana))
                assertFalse(sortTest(apple === banana))
                assertFalse(sortTest(plum === orange))
                assertFalse(sortTest(peach === banana))
        }

        test("sort function application"){
                assertTrue(sortTest(App("identity", apple) === apple))
                assertTrue(sortTest(App("doubleIdentity", banana, banana) === banana))
                assertTrue(sortTest(App("tripleIdentity", peach, peach, peach) === peach))
                assertFalse(sortTest(App("identity", plum) === apple))
                assertFalse(sortTest(App("doubleIdentity", peach, peach) === banana))
                assertFalse(sortTest(App("tripleIdentity", banana, banana, banana) === peach))
        }

        test("sort distinct"){
                assertTrue(sortTest(Distinct(apple, banana)))
                assertTrue(sortTest(Distinct(apple, banana, peach, plum, orange)))
                assertFalse(sortTest(Distinct(apple, apple)))
                assertFalse(sortTest(Distinct(apple, banana, peach, apple)))
                assertFalse(sortTest(Distinct(banana, banana, peach, plum, orange)))
        }

        test("sort forall"){
                val temp: Var = Var("temp")
                // Generic tests
                assertTrue(sortTest(Forall(temp of fruit, App("identity", temp) === temp)))
                assertTrue(sortTest(Forall(temp of fruit, App("doubleIdentity", temp, temp) === temp)))
                assertTrue(sortTest(Forall(temp of fruit, App("tripleIdentity", temp, temp, temp) === temp)))
                assertFalse(sortTest(Forall(temp of fruit, App("identity", temp) === apple)))
                assertFalse(sortTest(Forall(temp of fruit, App("doubleIdentity", banana, temp) === temp)))
                assertFalse(sortTest(Forall(temp of fruit, App("tripleIdentity", temp, peach, temp) === temp)))
                // Double binding
                assertTrue(sortTest(Forall(temp of fruit, Forall(temp of fruit, App("identity", temp) === temp))))
        }
}
