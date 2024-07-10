import org.scalatest._
import org.scalatest.flatspec._
import fortress.util.Seconds
import fortress.modelfinders._
import fortress.msfol._
import fortress.msfol.Term._
import fortress.transformers._
import fortress.config._

import scala.util.Using
import fortress.data.IntSuffixNameGenerator
import fortress.data.NameGenerator
import fortress.operations.SmtlibConverter
import fortress.problemstate._

import java.io.StringWriter
import fortress.util.Dump

class ClosureEliminatorVakiliTransformerTests extends UnitSuite {
    // Inputs are expected in NNF

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val A  = SortConst("A")
    
    val axy: Seq[AnnotatedVar] = Seq(x.of(A), y.of(A))

    val relation = FuncDecl("relation", Seq(A,A), Sort.Bool)

    val baseTheory = Theory.empty
        .withSort(A)
        .withFunctionDeclaration(relation)

    
    val manager = Manager.makeEmpty()
    manager.addOption(TypecheckSanitizeOption, 1)
    manager.addOption(EnumEliminationOption, 2)
    manager.addOption(IfLiftingOption,3)
    manager.addOption(NnfOption, 4)
    manager.addOption(new SimpleOption("NegativeClosureElim", ClosureEliminationVakiliTransformer), 4)
    manager.addOption(QuantifierExpansionOption, 5001)
    manager.addOption(RangeFormulaOption, 5002)
    manager.addOption(SimplifyOption, 5003)
    manager.addOption(DatatypeOption, 5004)


    def quickOutput(ps: ProblemState): Unit = {
        var result = TypecheckSanitizeTransformer(ps)
        result = EnumEliminationTransformer(ps)
        result = NnfTransformer(ps)
        result = ClosureEliminationVakiliTransformer(ps)
        println(Dump.problemStateToSmtlib(result))
    }

    test("positive ce unchanged"){
        val axiom = Closure("relation", x, y)
        val theory = baseTheory
            .withAxiom(axiom)
            .withFunctionDeclaration(FuncDecl("relation", A, A, BoolSort))
        
        val ps: ProblemState = ProblemState(theory)
            .withScopes(Map[Sort,Scope](A -> ExactScope(4)))
            .withFlags(Flags(haveRunNNF = true))

        ClosureEliminationVakiliTransformer(ps).theory should be (theory)
    }

    test("empty relation remains"){
        val relIsEmpty = Forall(axy,
            Not(App("emptyrel", x, y))
        )
        
        val somethingAdded = Forall(axy, Not(Closure("emptyrel", x, y)))

        val newTheory = baseTheory
            .withAxiom(relIsEmpty)
            .withAxiom(somethingAdded)
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("emptyrel", A, A, Sort.Bool))
        /*
        val ps: ProblemState = ProblemState(newTheory, Map[Sort,Scope](A -> ExactScope(4)))
        quickOutput(ps)
        */
        Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(newTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                val result = finder.checkSat()
                assert(result == (ModelFinderResult.Sat)) 
                
            }}
    }

    test("full relation remains") {
        val relIsFull = Forall(axy,App("fullrel", x, y))
        
        val somethingMissing = Exists(axy, Not(Closure("fullrel", x, y)))

        val newTheory = baseTheory
            .withAxiom(relIsFull)
            .withAxiom(somethingMissing)
            .withFunctionDeclaration(FuncDecl("fullrel", A, A, BoolSort))
        
        Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(newTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                val result = finder.checkSat()
                assert(result == (ModelFinderResult.Unsat)) 
            }}
    }

    test("treate a line properly"){
        val a = EnumValue("a")
        val b = EnumValue("b")
        val c = EnumValue("c")

        val A  = SortConst("A")

        val R = FuncDecl.mkFuncDecl("R", A, A, Sort.Bool)

        val initialOrder = Forall(axy,
            Iff(App(R.name, x, y),
                Or(
                    And(Eq(x, a), Eq(y, b)),
                    And(Eq(x, b), Eq(y, c))
                )
            )
        )

        // This is not enough Because we changed Iff to Implies.
        // There isn't a good way to do this for negatives only
        val correctClosure = Forall(axy,
            Implication(Or(
                    And(Eq(x, a), Eq(y, b)),
                    And(Eq(x, a), Eq(y, c)),
                    And(Eq(x, b), Eq(y, c)),
                ), 
                Closure(R.name, x, y)
            )
        )
        val correctReflexiveClosure = Forall(axy,
            Implication( Or(
                    Eq(x, y),
                    And(Eq(x, a), Eq(y, b)),
                    And(Eq(x, a), Eq(y, c)),
                    And(Eq(x, b), Eq(y, c))
                ),
                ReflexiveClosure(R.name, x, y)
            )
        )

        // isSufficient is positive, so we skip it
        //val defIsSufficient = Implication(initialOrder, And(correctClosure, correctReflexiveClosure))
        val defIsNotSufficient = And(initialOrder, Not(correctReflexiveClosure))
        val defIsNotSufficient2 = And(initialOrder, Not(correctClosure))
        
        /*
        val goodTheory = baseTheory
                        .withAxiom(defIsSufficient)
                        .withEnumSort(A, a, b, c)
                        .withFunctionDeclaration(R)
                        */
        val badTheory = baseTheory
                        .withAxiom(defIsNotSufficient)
                        .withEnumSort(A, a, b, c)
                        .withFunctionDeclaration(R)
        
        val badTheory2 = baseTheory
                        .withAxiom(defIsNotSufficient2)
                        .withEnumSort(A, a, b, c)
                        .withFunctionDeclaration(R)
        /*
        Using.resource(manager.setupModelFinder()){ finder => {
            finder.setTheory(goodTheory)
            finder.setExactScope(A, 3)
            finder.setTimeout(Seconds(10))
            assert(finder.checkSat() == (ModelFinderResult.Sat)) 
        }}
        */
        Using.resource(manager.setupModelFinder()){ finder => {
            finder.setTheory(badTheory)
            finder.setExactScope(A, 3)
            finder.setTimeout(Seconds(10))

            val result = finder.checkSat()
            // for debugging
            if (result == ModelFinderResult.Sat) {
                val modelstring = finder.viewModel().toString()
                print(modelstring)
            }
            assert(result == ModelFinderResult.Unsat) 
        }}

        Using.resource(manager.setupModelFinder()){ finder => {
            finder.setTheory(badTheory2)
            finder.setExactScope(A, 3)
            finder.setTimeout(Seconds(10))

            val result = finder.checkSat()
            if (result == ModelFinderResult.Sat) {
                val modelstring = finder.viewModel().toString()
                print(modelstring)
            }
            assert(result == ModelFinderResult.Unsat) 
        }}
    }
}