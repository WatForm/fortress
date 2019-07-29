import fortress.inputs.SmtLibSubsetParser.DistinctContext
import org.scalatest._
import org.junit.Assert._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import fortress.msfol._
import fortress.modelfind._
import fortress.interpretation._
import scala.collection.immutable.Seq

@RunWith(classOf[JUnitRunner])
class VerifyInterpretationTests extends FunSuite with Matchers {
        /** Unit tests for Theory.verifyInterpretation()
          *
          * In each function, we first create a raw theory with all our constant & function definitions,
          * then apply constraints (axioms) and pass it through Z3 to generate desired
          * values for the constants.
          *
          * We then test by appending individual axioms onto the raw theory and then
          * running it through the verifier to test that axiom with the interpretation we got back.
          */

        runBoolTests()
        runSortTests()
        runSortNoEnumTests()
        runIntTests()

        def injectAxiomAndTest(theory: Theory, interpretation: Interpretation)(axiom: Term): Boolean = {
                theory.withAxiom(axiom).verifyInterpretation(interpretation)
        }

        def runBoolTests(): Unit = {
                val bool: Sort = Sort.Bool

                val true1: Var = Var("true1")
                val true2: Var = Var("true2")
                val true3: Var = Var("true3")
                val false1: Var = Var("false1")
                val false2: Var = Var("false2")
                val false3: Var = Var("false3")

                val identity = FuncDecl("identity", bool, bool)
                val doubleIdentity = FuncDecl("doubleIdentity", bool, bool, bool)

                val rawTheory : Theory = Theory.empty
                    .withConstants(true1 of bool, true2 of bool, false1 of bool,
                            false2 of bool, true3 of bool, false3 of bool)
                    .withFunctionDeclarations(identity, doubleIdentity)

                val temp: Var = Var("temp")
                val theory: Theory = rawTheory
                    .withAxiom(And(true1, true2, true3))
                    .withAxiom(Not(Or(false1, false2, false3)))
                    .withAxiom(Forall(temp of bool, temp === App("identity", temp)))
                    .withAxiom(Forall(temp of bool, temp === App("doubleIdentity", temp, temp)))

                val finder: ModelFinder = ModelFinder.createDefault()
                try {
                        finder.setTheory(theory)
                        finder.checkSat()
                } catch {
                        case e: Throwable => e.printStackTrace()
                }

                val interpretation: Interpretation = finder.viewModel()
                val run: Term => Boolean = injectAxiomAndTest(rawTheory, interpretation)

                test("boolean true/false/not"){
                        assertTrue(run(true1))
                        assertTrue(run(Not(false1)))
                        assertFalse(run(Not(true1)))
                        assertFalse(run(false1))
                }

                test("boolean and/or"){
                        assertTrue(run(And(true1, true2, true3)))
                        assertTrue(run(Or(true1, false1, false2, false3)))
                        assertFalse(run(And(true1, true2, false1, false2)))
                        assertFalse(run(Or(false3)))
                }

                test("boolean implication/iff/eq"){
                        assertTrue(run(true1 === true2))
                        assertTrue(run(Not(true1) === false1))
                        assertTrue(run(true1 ==> true1))
                        assertTrue(run(false1 ==> true1))
                        assertTrue(run(false1 ==> false1))
                        assertTrue(run(Iff(true1, true2)))
                        assertTrue(run(Iff(false1, false2)))
                        assertFalse(run(true1 === false1))
                        assertFalse(run(true1 ==> false1))
                        assertFalse(run(Iff(true1, false1)))
                        assertFalse(run(Iff(false1, true1)))
                }

                test("boolean function application"){
                        assertTrue(run(App("identity", true1)))
                        assertTrue(run(App("doubleIdentity", true1, true3)))
                        assertFalse(run(App("identity", false1)))
                        assertFalse(run(App("doubleIdentity", false1, false3)))
                }

                test("boolean distinct"){
                        assertTrue(run(Distinct(true1, false2)))
                        assertTrue(run(Distinct(false3, true2)))
                        assertFalse(run(Distinct(false1, false2, true1)))
                }

                val tmp1: Var = Var("tmp1")
                val tmp2: Var = Var("tmp2")
                val tmp3: Var = Var("tmp3")
                test("boolean forall"){
                        assertTrue(run(Forall(tmp1 of bool, Or(tmp1, true1))))
                        assertTrue(run(Forall(tmp1 of bool, And(tmp1, tmp1) === tmp1)))
                        assertTrue(run(Forall(Seq(tmp1 of bool, tmp2 of bool), Or(tmp1 === tmp2, tmp1, tmp2))))
                        assertFalse(run(Forall(tmp1 of bool, tmp1)))
                        assertFalse(run(Forall(Seq(tmp1 of bool, tmp2 of bool), And(tmp1, tmp2))))
                }

                test("boolean exists"){
                        assertTrue(run(Exists(tmp1 of bool, tmp1)))
                        assertTrue(run(Exists(Seq(tmp1 of bool, tmp2 of bool, tmp3 of bool), And(tmp1, tmp2, tmp3))))
                        assertFalse(run(Exists(Seq(tmp1 of bool, tmp2 of bool), And(tmp1 === tmp2, Not(tmp1 === tmp2)))))
                }
        }

        def runSortNoEnumTests(): Unit = {
                // This is the exact same as the other Sort test but does not use an EnumSort this time
                val fruit: Sort = Sort.mkSortConst("fruit")

                val apple: Var = Var("apple")
                val orange: Var = Var("orange")
                val banana: Var = Var("banana")
                val plum: Var = Var("plum")
                val peach: Var = Var("peach")

                val identity: FuncDecl = FuncDecl("identity", fruit, fruit)
                val doubleIdentity: FuncDecl = FuncDecl("doubleIdentity", fruit, fruit, fruit)
                val tripleIdentity: FuncDecl = FuncDecl("tripleIdentity", fruit, fruit, fruit, fruit)

                val temp: Var = Var("temp")
                val rawTheory: Theory = Theory.empty
                    .withSort(fruit)
                    .withConstants(apple of fruit, orange of fruit,
                            banana of fruit, plum of fruit, peach of fruit)
                    .withFunctionDeclarations(identity, doubleIdentity, tripleIdentity)

                val theory: Theory = rawTheory
                    .withAxiom(Distinct(apple, orange, banana, plum, peach))
                    .withAxiom(Forall(temp of fruit, temp === App("identity", temp)))
                    .withAxiom(Forall(temp of fruit, temp === App("doubleIdentity", temp, temp)))
                    .withAxiom(Forall(temp of fruit, temp === App("tripleIdentity", temp, temp, temp)))

                val finder: ModelFinder = ModelFinder.createDefault()
                try {
                        finder.setTheory(theory)
                        finder.setAnalysisScope(fruit, 5)
                        finder.checkSat()
                } catch {
                        case e: Throwable => e.printStackTrace()
                }

                val interpretation: Interpretation = finder.viewModel()
                val run: Term => Boolean = injectAxiomAndTest(rawTheory, interpretation)

                test("sort (no enum) eq"){
                        assertTrue(run(apple === apple))
                        assertTrue(run(orange === orange))
                        assertTrue(run(plum === plum))
                        assertTrue(run(peach === peach))
                        assertTrue(run(banana === banana))
                        assertFalse(run(apple === banana))
                        assertFalse(run(plum === orange))
                        assertFalse(run(peach === banana))
                }

                test("sort (no enum) function application"){
                        assertTrue(run(App("identity", apple) === apple))
                        assertTrue(run(App("doubleIdentity", banana, banana) === banana))
                        assertTrue(run(App("tripleIdentity", peach, peach, peach) === peach))
                        assertTrue(run(App("identity", App("identity", banana)) === banana))
                        assertTrue(run(App("identity", App("identity", App("identity", banana))) === banana))
                        assertTrue(run(App("identity", App("identity", banana)) === App("identity", banana)))
                        assertTrue(run(App("doubleIdentity", App("identity", banana), App("identity", banana)) === App("identity", banana)))
                        assertFalse(run(App("identity", plum) === apple))
                        assertFalse(run(App("doubleIdentity", peach, peach) === banana))
                        assertFalse(run(App("tripleIdentity", banana, banana, banana) === peach))
                        assertFalse(run(App("identity", plum) === App("identity", apple)))
                        assertFalse(run(App("identity", App("identity", orange)) === App("identity", apple)))
                        assertFalse(run(App("doubleIdentity", App("identity", apple), App("identity", apple)) === App("identity", banana)))
                }

                test("sort (no enum) distinct"){
                        assertTrue(run(Distinct(apple, banana)))
                        assertTrue(run(Distinct(apple, banana, peach, plum, orange)))
                        assertFalse(run(Distinct(apple, apple)))
                        assertFalse(run(Distinct(apple, banana, peach, apple)))
                        assertFalse(run(Distinct(banana, banana, peach, plum, orange)))
                }

                test("sort (no enum) forall"){
                        val temp: Var = Var("temp")
                        val temp2: Var = Var("temp2")
                        // Generic tests
                        assertTrue(run(Forall(temp of fruit, App("identity", temp) === temp)))
                        assertTrue(run(Forall(temp of fruit, App("doubleIdentity", temp, temp) === temp)))
                        assertTrue(run(Forall(temp of fruit, App("tripleIdentity", temp, temp, temp) === temp)))
                        assertFalse(run(Forall(temp of fruit, App("identity", temp) === apple)))
                        assertFalse(run(Forall(temp of fruit, App("doubleIdentity", banana, temp) === temp)))
                        assertFalse(run(Forall(temp of fruit, App("tripleIdentity", temp, peach, temp) === temp)))
                        assertFalse(run(Forall(Seq(temp of fruit, temp2 of fruit), App("doubleIdentity", temp, temp2) === temp)))
                        // Double binding
                        assertTrue(run(Forall(temp of fruit, Forall(temp of fruit, App("identity", temp) === temp))))
                }

                test("sort (no enum) exists"){
                        val temp: Var = Var("temp")
                        val temp2: Var = Var("temp2")
                        // Generic tests
                        assertTrue(run(Exists(temp of fruit, App("identity", temp) === temp)))
                        assertTrue(run(Exists(temp of fruit, App("doubleIdentity", temp, temp) === temp)))
                        assertTrue(run(Exists(temp of fruit, App("tripleIdentity", temp, temp, temp) === temp)))
                        assertTrue(run(Exists(Seq(temp of fruit, temp2 of fruit), App("doubleIdentity", temp, temp2) === temp)))
                        assertFalse(run(Exists(temp of fruit, Not(App("identity", temp) === temp))))
                        assertFalse(run(Exists(temp of fruit, Not(App("doubleIdentity", temp, temp) === temp))))
                        assertFalse(run(Exists(temp of fruit, Not(App("tripleIdentity", temp, temp, temp) === temp))))
                        // Double binding
                        assertTrue(run(Exists(temp of fruit, Exists(temp of fruit, App("identity", temp) === temp))))
                }
        }

        def runSortTests(): Unit = {
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

                val identity: FuncDecl = FuncDecl("identity", fruit, fruit)
                val doubleIdentity: FuncDecl = FuncDecl("doubleIdentity", fruit, fruit, fruit)
                val tripleIdentity: FuncDecl = FuncDecl("tripleIdentity", fruit, fruit, fruit, fruit)

                val temp: Var = Var("temp")
                val rawTheory: Theory = Theory.empty
                    .withEnumSort(fruit, fruitVals)
                    .withConstants(apple of fruit, orange of fruit,
                            banana of fruit, plum of fruit, peach of fruit)
                    .withFunctionDeclarations(identity, doubleIdentity, tripleIdentity)

                val theory: Theory = rawTheory
                    .withAxiom(Distinct(apple, orange, banana, plum, peach))
                    .withAxiom(Forall(temp of fruit, temp === App("identity", temp)))
                    .withAxiom(Forall(temp of fruit, temp === App("doubleIdentity", temp, temp)))
                    .withAxiom(Forall(temp of fruit, temp === App("tripleIdentity", temp, temp, temp)))

                val finder: ModelFinder = ModelFinder.createDefault()
                try {
                        finder.setTheory(theory)
                        finder.checkSat()
                } catch {
                        case e: Throwable => e.printStackTrace()
                }

                val interpretation: Interpretation = finder.viewModel()
                val run: Term => Boolean = injectAxiomAndTest(rawTheory, interpretation)

                test("sort eq"){
                        assertTrue(run(apple === apple))
                        assertTrue(run(orange === orange))
                        assertTrue(run(plum === plum))
                        assertTrue(run(peach === peach))
                        assertTrue(run(banana === banana))
                        assertFalse(run(apple === banana))
                        assertFalse(run(plum === orange))
                        assertFalse(run(peach === banana))
                }

                test("sort function application"){
                        assertTrue(run(App("identity", apple) === apple))
                        assertTrue(run(App("doubleIdentity", banana, banana) === banana))
                        assertTrue(run(App("tripleIdentity", peach, peach, peach) === peach))
                        assertTrue(run(App("identity", App("identity", banana)) === banana))
                        assertTrue(run(App("identity", App("identity", App("identity", banana))) === banana))
                        assertTrue(run(App("identity", App("identity", banana)) === App("identity", banana)))
                        assertTrue(run(App("doubleIdentity", App("identity", banana), App("identity", banana)) === App("identity", banana)))
                        assertFalse(run(App("identity", plum) === apple))
                        assertFalse(run(App("doubleIdentity", peach, peach) === banana))
                        assertFalse(run(App("tripleIdentity", banana, banana, banana) === peach))
                        assertFalse(run(App("identity", plum) === App("identity", apple)))
                        assertFalse(run(App("identity", App("identity", orange)) === App("identity", apple)))
                        assertFalse(run(App("doubleIdentity", App("identity", apple), App("identity", apple)) === App("identity", banana)))
                }

                test("sort distinct"){
                        assertTrue(run(Distinct(apple, banana)))
                        assertTrue(run(Distinct(apple, banana, peach, plum, orange)))
                        assertFalse(run(Distinct(apple, apple)))
                        assertFalse(run(Distinct(apple, banana, peach, apple)))
                        assertFalse(run(Distinct(banana, banana, peach, plum, orange)))
                }

                test("sort forall"){
                        val temp: Var = Var("temp")
                        val temp2: Var = Var("temp2")
                        // Generic tests
                        assertTrue(run(Forall(temp of fruit, App("identity", temp) === temp)))
                        assertTrue(run(Forall(temp of fruit, App("doubleIdentity", temp, temp) === temp)))
                        assertTrue(run(Forall(temp of fruit, App("tripleIdentity", temp, temp, temp) === temp)))
                        assertFalse(run(Forall(temp of fruit, App("identity", temp) === apple)))
                        assertFalse(run(Forall(temp of fruit, App("doubleIdentity", banana, temp) === temp)))
                        assertFalse(run(Forall(temp of fruit, App("tripleIdentity", temp, peach, temp) === temp)))
                        assertFalse(run(Forall(Seq(temp of fruit, temp2 of fruit), App("doubleIdentity", temp, temp2) === temp)))
                        // Double binding
                        assertTrue(run(Forall(temp of fruit, Forall(temp of fruit, App("identity", temp) === temp))))
                }

                test("sort exists"){
                        val temp: Var = Var("temp")
                        val temp2: Var = Var("temp2")
                        // Generic tests
                        assertTrue(run(Exists(temp of fruit, App("identity", temp) === temp)))
                        assertTrue(run(Exists(temp of fruit, App("doubleIdentity", temp, temp) === temp)))
                        assertTrue(run(Exists(temp of fruit, App("tripleIdentity", temp, temp, temp) === temp)))
                        assertTrue(run(Exists(Seq(temp of fruit, temp2 of fruit), App("doubleIdentity", temp, temp2) === temp)))
                        assertFalse(run(Exists(temp of fruit, Not(App("identity", temp) === temp))))
                        assertFalse(run(Exists(temp of fruit, Not(App("doubleIdentity", temp, temp) === temp))))
                        assertFalse(run(Exists(temp of fruit, Not(App("tripleIdentity", temp, temp, temp) === temp))))
                        // Double binding
                        assertTrue(run(Exists(temp of fruit, Exists(temp of fruit, App("identity", temp) === temp))))
                }
        }

        def runIntTests(): Unit = {
                val int: Sort = Sort.Int

                val zero: Var = Var("zero")
                val one: Var = Var("one")
                val three: Var = Var("three")
                val seven: Var = Var("seven")

                val rawTheory: Theory = Theory.empty
                    .withConstants(zero of int, one of int, three of int, seven of int)

                val theory: Theory = rawTheory
                    .withAxiom(IntegerLiteral(0) === zero)
                    .withAxiom(IntegerLiteral(1) === one)
                    .withAxiom(IntegerLiteral(3) === three)
                    .withAxiom(IntegerLiteral(7) === seven)

                val finder: ModelFinder = ModelFinder.createDefault()
                try {
                        finder.setTheory(theory)
                        finder.checkSat()
                } catch {
                        case e: Throwable => e.printStackTrace()
                }

                val interpretation: Interpretation = finder.viewModel()
                val run: Term => Boolean = injectAxiomAndTest(rawTheory, interpretation)

                test("int eq"){
                        assertTrue(run(zero === IntegerLiteral(0)))
                        assertTrue(run(seven === IntegerLiteral(7)))
                        assertFalse(run(one === IntegerLiteral(7)))
                        assertFalse(run(three === IntegerLiteral(0)))
                }

                test("int builtins"){
                        assertTrue(run(BuiltinApp(IntPlus, zero, one) === IntegerLiteral(1)))
                        assertTrue(run(BuiltinApp(IntPlus, BuiltinApp(IntPlus, one, one), one) === IntegerLiteral(3)))
                        assertFalse(run(BuiltinApp(IntPlus, three, seven) === IntegerLiteral(0)))
                        assertFalse(run(BuiltinApp(IntPlus, BuiltinApp(IntPlus, one, zero), one) === IntegerLiteral(3)))

                        assertTrue(run(BuiltinApp(IntSub, one, zero) === IntegerLiteral(1)))
                        assertTrue(run(BuiltinApp(IntSub, BuiltinApp(IntSub, one, zero), one) === IntegerLiteral(0)))
                        assertFalse(run(BuiltinApp(IntSub, one, zero) === IntegerLiteral(3)))
                        assertFalse(run(BuiltinApp(IntSub, BuiltinApp(IntSub, one, zero), one) === IntegerLiteral(7)))

                        assertTrue(run(BuiltinApp(IntNeg, zero) === IntegerLiteral(0)))
                        assertFalse(run(BuiltinApp(IntNeg, one) === IntegerLiteral(0)))

                        assertTrue(run(BuiltinApp(IntMult, one, one) === IntegerLiteral(1)))
                        assertFalse(run(BuiltinApp(IntMult, one, one) === IntegerLiteral(3)))

                        assertTrue(run(BuiltinApp(IntDiv, seven, three) === IntegerLiteral(2)))
                        assertTrue(run(BuiltinApp(IntDiv, seven, one) === IntegerLiteral(7)))
                        assertTrue(run(BuiltinApp(IntDiv, zero, one) === IntegerLiteral(0)))
                        assertFalse(run(BuiltinApp(IntDiv, seven, three) === IntegerLiteral(1)))

                        assertTrue(run(BuiltinApp(IntMod, seven, three) === IntegerLiteral(1)))
                        assertTrue(run(BuiltinApp(IntMod, seven, one) === IntegerLiteral(0)))
                        assertTrue(run(BuiltinApp(IntMod, zero, one) === IntegerLiteral(0)))
                        assertFalse(run(BuiltinApp(IntMod, seven, three) === IntegerLiteral(0)))

                        assertTrue(run(BuiltinApp(IntLE, zero, one)))
                        assertTrue(run(BuiltinApp(IntLE, one, one)))
                        assertFalse(run(BuiltinApp(IntLE, seven, one)))

                        assertTrue(run(BuiltinApp(IntLT, one, seven)))
                        assertFalse(run(BuiltinApp(IntLT, one, one)))
                        assertFalse(run(BuiltinApp(IntLT, one, zero)))

                        assertTrue(run(BuiltinApp(IntGE, one, zero)))
                        assertTrue(run(BuiltinApp(IntGE, one, one)))
                        assertFalse(run(BuiltinApp(IntGE, one, seven)))

                        assertTrue(run(BuiltinApp(IntGT, seven, one)))
                        assertFalse(run(BuiltinApp(IntGT, one, one)))
                        assertFalse(run(BuiltinApp(IntGT, zero, one)))
                }
        }
}
