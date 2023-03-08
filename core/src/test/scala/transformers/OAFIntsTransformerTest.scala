import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._
import fortress.config._
import scala.util.Using
import fortress.util.Seconds
import fortress.modelfind.ModelFinderResult
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._


class OAFIntsTransformerTest extends UnitSuite {
    val transformer = OAFIntsTransformer
    val intSize = 8
    val min = -4
    val max = 3
    val intScope = ExactScope(intSize, true)
    val simpleIntScopes = Map[Sort, Scope](IntSort -> intScope)

    val manager = Manager.makeEmpty()
    manager.addOption(TypecheckSanitizeOption, 1)
    manager.addOption(EnumEliminationOption, 2)


    // Add in this closure eliminator
    manager.addOption(new ToggleOption("OAFInts", _.addTransformer(transformer)), 102)

    //manager.addOption(QuantifierExpansionOption, 5001)
    manager.addOption(RangeFormulaOption, 5002)
    manager.addOption(SimplifyOption, 5003)
    //manager.addOption(DatatypeOption, 5004)
    manager.addOption(new ToggleOption("DomainElimination", _.addTransformer(DomainEliminationTransformer)), 5005)

    val aSort = SortConst("A")
    val x = Var("x")
    val y = Var("y")
    // This can fail, it's not robust, just for tests
    def axiomWithoutDistinct(axioms: Seq[Term]): Term = {
        axioms.filterNot(_ match {case Distinct(arguments) => true case _ => false})(0)
    }

    test("basic literals") {
        val axiom = Eq(IntegerLiteral(1), IntegerLiteral(2))
        val theory = Theory.empty
        .withAxiom(axiom)

        val problemState = ProblemState(theory, simpleIntScopes)

        val result = transformer(problemState)
        // we should now have two sorts of size 16
        result.scopes.values.toSeq shouldBe Seq(intScope, intScope)
        // Overflow is applied to equality
        val resultAxioms = result.theory.axioms.toSeq
        resultAxioms should have length (1)
        // fiter out distinct
        val transformedEq = resultAxioms(0)
        transformedEq should matchPattern {
            case AndList(Seq(
                Eq(IntegerLiteral(1), IntegerLiteral(2)),
                AndList(Seq(
                    App(check1, Seq(IntegerLiteral(1))),
                    App(check2, Seq(IntegerLiteral(2)))
                ))
            )) if check1 == check2 =>
        }
        val resultSig = result.theory.signature
        resultSig.functionDefinitions should have size (3)
        //transformedEq should matchPattern {case Not(_) => }
    }

    test("large literals") {
        // Similar to normal literals but also has a negation!
        val axiom = Not(Term.mkGE(IntegerLiteral(1000), IntegerLiteral(2)))
        val theory = Theory.empty
        .withAxiom(axiom)

        val problemState = ProblemState(theory, simpleIntScopes)

        val result = transformer(problemState)
        // we should now have two sorts of size 16
        result.scopes.values.toSeq shouldBe Seq(intScope, intScope)
        // Overflow is applied to equality
        val resultAxioms = result.theory.axioms.toSeq
        resultAxioms should have length (1)
        // fiter out distinct
        val transformedGE = resultAxioms(0)
        transformedGE should matchPattern {
            case Not(OrList(Seq(
                BuiltinApp(IntGE, Seq(IntegerLiteral(1000), IntegerLiteral(2))),
                Not(AndList(Seq(
                    App(check1, Seq(IntegerLiteral(1000))),
                    App(check2, Seq(IntegerLiteral(2)))
                )))
            ))) if check1 == check2 =>
        }
    }

    test("variables") {
        val axiom = Eq(Term.mkPlus(x, x), y)
        val sig = Signature.empty
            .withConstants(x.of(IntSort), y.of(IntSort))
        val theory = Theory(sig, Set(axiom))
        val problemState = ProblemState(theory, simpleIntScopes)
        val result = transformer(problemState)
        
        //constants should be x, y of the same Sort
        val resultConstants = result.theory.signature.constants
        resultConstants.map(_.variable) should be (Set(x,y))
        // seq first so set doesn't combine the identical sorts
        val constantSorts = resultConstants.toSeq.map(_.sort)
        constantSorts(0) should be (constantSorts(1))

        // check the remaining axiom
        result.theory.axioms should have size (1)
        val resultAxiom = result.theory.axioms.toSeq(0)
        // x+x needs a check, y should not need a check
        resultAxiom should matchPattern {
            case AndList(Seq(
                Eq(
                    BuiltinApp(IntPlus, Seq(App(_, Seq(Var("x"))), App(_, Seq(Var("x"))))),
                    App(_, Seq(Var("y")))
                ),
                App(_, Seq(BuiltinApp(IntPlus, Seq(App(_, Seq(Var("x"))), App(_, Seq(Var("x")))))))
            )) =>
        }
    }


    test("integer predicates") {
        val fDec = FuncDecl("f", IntSort, aSort, BoolSort)
        val axiomSimple = App("f", x, y)
        val axiomAddition = App("f", Term.mkPlus(x, IntegerLiteral(1)), y)

        val sig = Signature.empty
            .withSort(aSort)
            .withConstants(x.of(IntSort), y.of(aSort))
            .withFunctionDeclaration(fDec)
        val theory1 = Theory(sig, Set(axiomSimple))
        val problemState1 = ProblemState(theory1, simpleIntScopes)

        val result1 = transformer(problemState1)
        val resultTheory: Theory = result1.theory

        resultTheory.signature.functionDeclarations should have size (1)
        val fNewDec = resultTheory.signature.functionDeclarations.toSeq(0)
        // declaration should have changed intsort
        fNewDec should matchPattern {
            case FuncDecl("f", Seq(_, a), BoolSort) =>
        }

        // original axiom and the Distinct axiom
        resultTheory.axioms should have size (1)
        val transformedApp = (resultTheory.axioms.toSeq)(0)

        // We don't expect x to overflow, so no overflow is applied here
        transformedApp shouldBe axiomSimple

        val theory2 = Theory(sig, Set(axiomAddition))
        val ps2 = ProblemState(theory2, simpleIntScopes)
        val result2 = transformer(ps2)

        val resultAxiom2 = (result2.theory.axioms.toSeq)(0)
        resultAxiom2 should matchPattern {
            case AndList(Seq( // f(fromInt(toInt([x])+1)) && Inbounds(toInt(x)+1)
                App("f", Seq( // f(...
                    App(_, Seq( // fromInt
                        BuiltinApp(IntPlus, Seq(// toInt(x) + 1
                            App(_, Seq(x1)), // toInt(x)
                            IntegerLiteral(1)
                        )) 
                    )),
                    y
                )),
                // In range
                App(_, Seq( // TODO arg to isInBound is being wrapped in fromInt, which is wrong!!!
                    BuiltinApp(IntPlus, Seq( // toInt(x) + 1
                        App(_, Seq(x2)), IntegerLiteral(1)
                    ))
                ))
            )) =>
        }
    }

    test("integration works") {
        val negatedTautology = Not(
            Forall(Seq(x.of(IntSort), y.of(IntSort)),
                Implication(
                    And(
                        Term.mkGT(x, IntegerLiteral(0)),
                        Term.mkGT(y, IntegerLiteral(0))
                    ),
                    And(
                        Term.mkGT(Term.mkPlus(x, y), IntegerLiteral(0)),
                        Term.mkGT(Term.mkPlus(x, y), x),
                        Term.mkGT(Term.mkPlus(x, y), y)
                    )
                )
            )
        )

        val theory = Theory.empty
            .withAxiom(negatedTautology)
        //val problemState = ProblemState(theory, simpleIntScopes)

        /*  DEBUG
        val compiler = manager.setupCompiler()
        val result = compiler.compile(theory, simpleIntScopes, Seconds(10).toMilli, Seq.empty)
        result match {
            case Right(res) => {
                println("---Theory---")
                println(res.theory.smtlib)
                //println("--defns--")
                //println(res.theory.signature.functionDefinitions)
            }
            case _ => () 
        }
        */

        Using.resource(manager.setupModelFinder()){finder =>{
            finder.setTheory(theory)
            finder.setExactScope(IntSort, intSize)
            finder.setTimeout(Seconds(10))
            
            val result = finder.checkSat()
            if (result == ModelFinderResult.Sat){
                val modelstring = finder.viewModel().toString()
                println(modelstring)
                fail("Should be UNSAT")
            }
            assert(result == ModelFinderResult.Unsat)
        }}



    }
}