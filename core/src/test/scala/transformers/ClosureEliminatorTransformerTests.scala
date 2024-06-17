import org.scalatest._
import org.scalatest.flatspec._
import fortress.util.Seconds
import fortress.modelfind._
import fortress.msfol._
import fortress.msfol.Term._
import fortress.transformers._
import fortress.config._

import scala.util.Using
import fortress.data.IntSuffixNameGenerator
import fortress.operations.ClosureEliminatorEijck
import fortress.data.NameGenerator
import fortress.operations.SmtlibConverter
import fortress.problemstate._

import java.io.StringWriter
import fortress.util.Dump
import fortress.util.Milliseconds

// This should eventually be more of an integration test
// See https://www.scalatest.org/user_guide/sharing_tests

// This testing makes sure that we see behavior once, but not always...

// These use mkClosure because the arguments value of Closure still exists
// TODO how to select eliminator?
trait CETransfomerBehaviors{ this: AnyFlatSpec =>

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val A  = SortConst("A")
    
    val axy: Seq[AnnotatedVar] = Seq(x.of(A), y.of(A))

    val relation = FuncDecl("relation", Seq(A,A), Sort.Bool)

    val baseTheory = Theory.empty
        .withSort(A)
        .withFunctionDeclaration(relation)


    def anyClosureEliminationTransformer(newCE: ClosureEliminationTransformer): Unit = {

        //behavior of "A Closure Eliminator"

        // Create a barebones modelfinder configuration
        // This may be better as a fixture?
        val manager = Manager.makeEmpty()
        manager.addOption(TypecheckSanitizeOption, 1)
        manager.addOption(EnumEliminationOption, 2)
        

        // Add in this closure eliminator
        manager.addOption(new ToggleOption("ClosureElim", _.addTransformer(newCE)), 102)
        
        manager.addOption(QuantifierExpansionOption, 5001)
        manager.addOption(RangeFormulaOption, 5002)
        manager.addOption(SimplifyOption, 5003)
        manager.addOption(DatatypeOption, 5004)

        // TODO shouldn't change anything without a closure
        
        it should "be able to connect all arbitrary points" in {
            val allConnected = Forall(Seq(x.of(A), y.of(A)),
                Term.mkClosure("arbitraryRelation", x, y)
            )
            val newTheory = baseTheory
                .withAxiom(allConnected)
                .withFunctionDeclaration(FuncDecl.mkFuncDecl("arbitraryRelation", A, A, Sort.Bool))

            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(newTheory)
                finder.setExactScope(A, 4)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
        }

        it should "transformProperly" in {
            val everything= Forall(Seq(x of A, y of A),
                Term.mkClosure("relation", x, y)
            )
            val theory = baseTheory
                .withAxiom(everything)
            val ps = ProblemState(theory, Map(A -> ExactScope(4)))
            val result = newCE(ps)

            assert(result.theory.axioms  contains  (Forall(Seq(x of A, y of A), App("^relation", x, y))),
                f"Resulting axioms ${result.theory.axioms} does not contain the correct replacement for the app")
        }

        it should "eliminate in definitions" in {
            val theory = baseTheory
                .withConstantDefinition(
                    ConstantDefinition(Var("cDef") of BoolSort, Term.mkClosure("relation", x, y))
                )
                .withFunctionDefinition(FunctionDefinition(
                    "fDef", Seq(x of A), BoolSort,
                    Term.mkClosure("relation", x, y)
                ))
                .withConstantDeclaration(y of A)
            val ps = ProblemState(theory, Map(A -> ExactScope(4)))
            val result = newCE(ps)

            val cDefsWithClosures = result.theory.constantDefinitions.filter(_.body match {
                case Closure(_,_,_,_) => true
                case _ => false
            })
            assert(cDefsWithClosures.isEmpty, f"Constant Definitions should not contain closures but got: ${cDefsWithClosures}")
            val fDefsWithClosures = result.theory.functionDefinitions.filter(_.body match {
                case Closure(_,_,_,_) => true
                case _ => false
            })
            assert(fDefsWithClosures.isEmpty, f"Function Definitions should not contain closures but got: ${fDefsWithClosures}")
        }

        it should "treat an empty relation properly" in {
            // No elements in the relation 
            val relIsEmpty = Forall(x.of(A),
                Not(Exists(y.of(A),
                    App("emptyrel", x, y)
                ))
            )
            val somethingWrong = Exists(axy,
                Or(
                    Term.mkClosure("emptyrel", x, y),
                    And(Term.mkReflexiveClosure("emptyrel", x, y), Not(Eq(x, y)))
                )
            )

            val newTheory = baseTheory
                .withAxiom(relIsEmpty)
                //.withAxiom(reflexiveOnly)
                //.withAxiom(closureAddsNothing)
                .withAxiom(somethingWrong)
                .withFunctionDeclaration(FuncDecl.mkFuncDecl("emptyrel", A, A, Sort.Bool))
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(newTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                val result = finder.checkSat()
                assert(result == (ModelFinderResult.Unsat)) 
            }}

        }

        it should "treat a line properly" in {
            // TODO define above fix!
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

            val correctClosure = Forall(axy,
                Iff(
                    Closure(R.name, x, y),
                    Or(
                        And(Eq(x, a), Eq(y, b)),
                        And(Eq(x, a), Eq(y, c)),
                        And(Eq(x, b), Eq(y, c)),
                    )
                )
            )
            /*
            val correctReflexiveClosure = Forall(axy,
                Iff(ReflexiveClosure(R.name, Seq(x,y), x, y),
                    Or(Eq(x,y), Closure(R.name, Seq(x,y), x, y))
                )
            )
            */
            val correctReflexiveClosure = Forall(axy,
                Iff(
                    ReflexiveClosure(R.name, x, y),
                    Or(
                        Eq(x, y),
                        And(Eq(x, a), Eq(y, b)),
                        And(Eq(x, a), Eq(y, c)),
                        And(Eq(x, b), Eq(y, c))
                    )
                )
            )

            val defIsSufficient = Implication(initialOrder, And(correctClosure, correctReflexiveClosure))
            val defIsNotSufficient = And(initialOrder, Not(correctReflexiveClosure))
            val defIsNotSufficient2 = And(initialOrder, Not(correctClosure))

            val goodTheory = baseTheory
                            .withAxiom(defIsSufficient)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            val badTheory = baseTheory
                            .withAxiom(defIsNotSufficient)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
            val badTheory2 = baseTheory
                            .withAxiom(defIsNotSufficient2)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(goodTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
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

        it should "work with fixed arguments" in {
            // TODO define above fix!
            val a = EnumValue("a")
            val b = EnumValue("b")
            val c = EnumValue("c")

            val A  = SortConst("A")

            val R = FuncDecl.mkFuncDecl("R", A, A, Sort.Bool, Sort.Bool)

            val initialOrder = Forall(axy :+ z.of(Sort.Bool),
                Iff(App(R.name, x, y, z),
                    Or(
                        And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                        And(Eq(x, b), Eq(y, c), Eq(z, Top))
                    )
                )
            )

            val correctClosure = Forall(axy :+ z.of(Sort.Bool),
                Iff(
                    Closure(R.name, x, y, Seq(z)),
                    Or(
                        And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                        And(Eq(x, a), Eq(y, c), Eq(z, Top)),
                        And(Eq(x, b), Eq(y, c), Eq(z, Top)),
                    )
                )
            )
            /*
            val correctReflexiveClosure = Forall(axy,
                Iff(ReflexiveClosure(R.name, Seq(x,y), x, y),
                    Or(Eq(x,y), Closure(R.name, Seq(x,y), x, y))
                )
            )
            */
            val m = Var("m")
            val n = Var("n")
            val o = Var("o")
            /*
            val correctReflexiveClosure = Forall(axy appended z.of(Sort.Bool),
                Iff(
                    ReflexiveClosure(R.name, x, y, Seq(z)),
                    Or(
                        Eq(x, y),
                        And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                        And(Eq(x, a), Eq(y, c), Eq(z, Top)),
                        And(Eq(x, b), Eq(y, c), Eq(z, Top))
                    )
                )
            )
            */
            val correctReflexiveClosure = Forall(Seq(m.of(A), n.of(A), o.of(BoolSort)),
                Iff(
                    ReflexiveClosure(R.name, m, n, Seq(o)),
                    Or(
                        Eq(m, n),
                        And(Eq(m, a), Eq(n, b), Eq(o, Top)),
                        And(Eq(m, a), Eq(n, c), Eq(o, Top)),
                        And(Eq(m, b), Eq(n, c), Eq(o, Top))
                    )
                )
            )
            val defIsSufficient = Implication(initialOrder, And(correctClosure, correctReflexiveClosure))
            val defIsNotSufficient = And(initialOrder, Not(correctReflexiveClosure))
            val defIsNotSufficient2 = And(initialOrder, Not(correctClosure))
            val goodTheory = baseTheory
                .withAxiom(defIsSufficient)
                .withEnumSort(A, a, b, c)
                .withFunctionDeclaration(R)
            val badTheory = baseTheory
                            .withAxiom(defIsNotSufficient)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
            val badTheory2 = baseTheory
                            .withAxiom(defIsNotSufficient2)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
                            
            /*
            // Use to get a debug dump. Will break tests
            manager.removeOption("QuantifierExpansion")
            val comp = manager.setupCompiler()
            val simpleTheory = baseTheory.withAxiom(correctReflexiveClosure).withEnumSort(A, a, b, c).withFunctionDeclaration(R)
            val mp = Map[Sort, Int](A -> 3)
            val timeoutGiven = Seconds(200).toMilli
            val compresult = comp.compile(simpleTheory, mp, timeoutGiven, Seq.empty)

            compresult match {
                case Right(result) => {
                    println("===============")
                    println(Dump.theoryToSmtlib(result.theory))
                    println("===============")
                    result.theory.axioms.foreach {
                        axiom => println(Dump.termToSmtlib(axiom))
                    }
                    println("===============")
                }
                case _ => ()
            }
            // end of debug section
            */
            
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(goodTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
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

        it should "work on functions" in {
            // TODO define above fix!
            val a = EnumValue("a")
            val b = EnumValue("b")
            val c = EnumValue("c")

            val A  = SortConst("A")

            val R = FuncDecl.mkFuncDecl("R", A, A)

            val initialOrder = Forall(axy,
                Iff(Eq(App(R.name, x), y),
                    Or(
                        And(Eq(x, a), Eq(y, b)),
                        And(Eq(x, b), Eq(y, c))
                    )
                )
            )

            val correctClosure = Forall(axy,
                Iff(
                    Closure(R.name, x, y),
                    Or(
                        And(Eq(x, a), Eq(y, b)),
                        And(Eq(x, a), Eq(y, c)),
                        And(Eq(x, b), Eq(y, c)),
                    )
                )
            )
            
            val correctReflexiveClosure = Forall(axy,
                Iff(
                    ReflexiveClosure(R.name, x, y),
                    Or(
                        Eq(x, y),
                        And(Eq(x, a), Eq(y, b)),
                        And(Eq(x, a), Eq(y, c)),
                        And(Eq(x, b), Eq(y, c))
                    )
                )
            )

            val defIsSufficient = Implication(initialOrder, And(correctClosure, correctReflexiveClosure))
            val defIsNotSufficient = And(initialOrder, Not(correctReflexiveClosure))
            val defIsNotSufficient2 = And(initialOrder, Not(correctClosure))

            val goodTheory = baseTheory
                            .withAxiom(defIsSufficient)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            val badTheory = baseTheory
                            .withAxiom(defIsNotSufficient)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
            val badTheory2 = baseTheory
                            .withAxiom(defIsNotSufficient2)
                            .withEnumSort(A, a, b, c)
                            .withFunctionDeclaration(R)
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(goodTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
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

        it should "close over definitions" in {
            val a = EnumValue("a")
            val b = EnumValue("b")
            val c = EnumValue("c")

            val A  = SortConst("A")

            val R = FunctionDefinition("R", Seq(x.of(A), y.of(A), z.of(BoolSort)), BoolSort,
                Or(
                    And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                    And(Eq(x, b), Eq(y, c), Eq(z, Top))
                )
            )
            val correctClosure = Forall(axy :+ z.of(Sort.Bool),
                Iff(
                    Closure(R.name, x, y, Seq(z)),
                    Or(
                        And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                        And(Eq(x, a), Eq(y, c), Eq(z, Top)),
                        And(Eq(x, b), Eq(y, c), Eq(z, Top)),
                    )
                )
            )
            /*
            val correctReflexiveClosure = Forall(axy,
                Iff(ReflexiveClosure(R.name, Seq(x,y), x, y),
                    Or(Eq(x,y), Closure(R.name, Seq(x,y), x, y))
                )
            )
            */
            val m = Var("m")
            val n = Var("n")
            val o = Var("o")
            /*
            val correctReflexiveClosure = Forall(axy appended z.of(Sort.Bool),
                Iff(
                    ReflexiveClosure(R.name, x, y, Seq(z)),
                    Or(
                        Eq(x, y),
                        And(Eq(x, a), Eq(y, b), Eq(z, Top)),
                        And(Eq(x, a), Eq(y, c), Eq(z, Top)),
                        And(Eq(x, b), Eq(y, c), Eq(z, Top))
                    )
                )
            )
            */
            val correctReflexiveClosure = Forall(Seq(m.of(A), n.of(A), o.of(BoolSort)),
                Iff(
                    ReflexiveClosure(R.name, m, n, Seq(o)),
                    Or(
                        Eq(m, n),
                        And(Eq(m, a), Eq(n, b), Eq(o, Top)),
                        And(Eq(m, a), Eq(n, c), Eq(o, Top)),
                        And(Eq(m, b), Eq(n, c), Eq(o, Top))
                    )
                )
            )
            val defIsSufficient = And(correctClosure, correctReflexiveClosure)
            val defIsNotSufficient = Not(correctReflexiveClosure)
            val defIsNotSufficient2 = Not(correctClosure)

            val basicTheory = baseTheory
                .withFunctionDefinition(R)
                .withEnumSort(A, a, b, c)
                
            val goodTheory = basicTheory
                .withAxiom(defIsSufficient)

            val badTheory = basicTheory
                            .withAxiom(defIsNotSufficient)
            
            val badTheory2 = basicTheory
                            .withAxiom(defIsNotSufficient2)
            
                            
            /*
            // Use to get a debug dump. Will break tests
            manager.removeOption("QuantifierExpansion")
            val comp = manager.setupCompiler()
            val simpleTheory = baseTheory.withAxiom(correctReflexiveClosure).withEnumSort(A, a, b, c).withFunctionDeclaration(R)
            val mp = Map[Sort, Int](A -> 3)
            val timeoutGiven = Seconds(200).toMilli
            val compresult = comp.compile(simpleTheory, mp, timeoutGiven, Seq.empty)

            compresult match {
                case Right(result) => {
                    println("===============")
                    println(Dump.theoryToSmtlib(result.theory))
                    println("===============")
                    result.theory.axioms.foreach {
                        axiom => println(Dump.termToSmtlib(axiom))
                    }
                    println("===============")
                }
                case _ => ()
            }
            // end of debug section
            */
            
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(goodTheory)
                finder.setExactScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
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
}

class ClosureEliminationIterativeTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationIterativeTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationIterativeTransformer)
}

class ClosureEliminationEijckTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationEijckTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationEijckTransformer)
}

class ClosureEliminationSquareTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationSquareTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationSquareTransformer)
}

class ClosureEliminationLiuTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationLiuTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationLiuTransformer)
}

class ClosureEliminationClaessenTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationClaessenTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationClaessenTransformer)
}

class ClosureEliminatorTransformerTest extends UnitSuite {
    val A = SortConst("A")
    val B = SortConst("B")
    val C = SortConst("C")

    val sortMap: Map[Sort, Scope] = Map(A -> ExactScope(5), B -> ExactScope(5), C -> ExactScope(5))

    test("correct trailing sorts"){
        val f1 = FuncDecl("f1", A, A, B, C, BoolSort)
        val f2 = FuncDecl("f2", A, A, BoolSort)
        val f3 = FuncDecl("f3", A, A, A, BoolSort)

        val sig = Signature.empty
            .withSorts(A,B,C)
            .withFunctionDeclarations(f1, f2, f3)

            // These are the defined functions in the abstract class
            // Testing with a subclass that does not overwrite
            val ce: ClosureEliminatorEijck = new ClosureEliminatorEijck(Top, sig, sortMap, new IntSuffixNameGenerator(Set(), 0))

            ce.visitor.getFixedSorts("f1") should equal (Seq(B, C))
            ce.visitor.getFixedSorts("f2") should equal (Seq())
            ce.visitor.getFixedSorts("f3") should equal (Seq(A))

            ce.visitor.getFixedAVars("f1") should have length 2
            ce.visitor.getFixedAVars("f2") should have length 0
            ce.visitor.getFixedAVars("f3") should have length 1

            ce.visitor.getFixedVars(0) should have length 0
            ce.visitor.getFixedVars(5) should have length 5 
    }
}