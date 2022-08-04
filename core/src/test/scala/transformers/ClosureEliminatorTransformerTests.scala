import org.scalatest._
import org.scalatest.flatspec._

import fortress.util.Seconds
import fortress.modelfind._
import fortress.msfol._
import fortress.msfol.Term._

import fortress.transformers._
import fortress.config._

import scala.util.Using
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
                finder.setAnalysisScope(A, 4, isExact = true)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
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
                finder.setAnalysisScope(A, 3, isExact = true)
                finder.setTimeout(Seconds(10))
                val result = finder.checkSat()
                assert(result == (ModelFinderResult.Unsat)) 
            }}

        }

        it should "connect a line" in {
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
                finder.setAnalysisScope(A, 3, isExact = true)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(badTheory)
                finder.setAnalysisScope(A, 3, isExact = true)
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
                finder.setAnalysisScope(A, 3, isExact = true)
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
                finder.setAnalysisScope(A, 3, isExact = true)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(badTheory)
                finder.setAnalysisScope(A, 3, isExact = true)
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
                finder.setAnalysisScope(A, 3, isExact = true)
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

class ClosureEliminationEijckTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationEijckTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationEijckTransformer)
}

class ClosureEliminationSquareTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationSquareTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationSquareTransformer)
}

class ClosureEliminationLiuTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationLiuTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationLiuTransformer)
}

class ClosureEliminationClaessenTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationClaessenTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationClaessenTransformer)
}

