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

    val relation = FuncDecl("relation", Seq(A,A), Sort.Bool)

    val baseTheory = Theory.empty
        .withSort(A)
        .withFunctionDeclaration(relation)


    def anyClosureEliminationTransformer(newCE: ClosureEliminationTransformer): Unit = {

        //behavior of "A Closure Eliminator"

        // Create a barebones modelfinder configuration
        // This may be better as a fixture?
        val manager = Manager.makeEmpty()
        manager.addOption(TypecheckSanitizeOption, 5001)
        // Add in this closure eliminator
        manager.addOption(new ToggleOption("ClosureElim", _.addTransformer(newCE)), 5002)
        manager.addOption(QuantifierExpansionOption, 5501)
        manager.addOption(RangeFormulaOption, 5502)
        manager.addOption(SimplifyOption, 5503)
        manager.addOption(DatatypeOption, 5504)

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
                finder.setAnalysisScope(A, 4)
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
            // Reflexive adds x<->x and nothing else
            val reflexiveOnly = Forall(Seq(x.of(A), y.of(A)),
                Iff(
                    mkReflexiveClosure("emptyrel", x, y),
                    Eq(x,y)
                )
            )
            // Closure remains empty
            val closureAddsNothing = Forall(Seq(x.of(A), y.of(A)),
                Not(mkClosure("emptyrel", x, y))
            )

            val newTheory = baseTheory
                .withAxiom(relIsEmpty)
                .withAxiom(reflexiveOnly)
                .withAxiom(closureAddsNothing)
                .withFunctionDeclaration(FuncDecl.mkFuncDecl("emptyrel", A, A, Sort.Bool))
            
            Using.resource(manager.setupModelFinder()){ finder => {
                finder.setTheory(newTheory)
                finder.setAnalysisScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}

        }
    }
}

class ClosureEliminationTransformerTest extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationTransformer)
}

class ClosureEliminationEijckTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationEijckTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationEijckTransformer)
}

class ClosureEliminationSquareTransformer extends AnyFlatSpec with CETransfomerBehaviors {
    "ClosureEliminationSquareTransformer" should behave like anyClosureEliminationTransformer(ClosureEliminationSquareTransformer)
}


