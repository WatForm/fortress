import org.scalatest._
import org.scalatest.flatspec._

import fortress.util.Seconds
import fortress.modelfind._
import fortress.msfol._
import fortress.msfol.Term._

import fortress.operations._

import scala.util.Using
// This should eventually be more of an integration test
// See https://www.scalatest.org/user_guide/sharing_tests

// This testing makes sure that we see behavior once, but not always...

// These use mkClosure because the arguments value of Closure still exists
// TODO how to select eliminator?
trait ClosureEliminatorBehaviors{ this: AnyFlatSpec =>

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val A  = SortConst("A")

    val relation = FuncDecl("relation", Seq(A,A), Sort.Bool)

    val baseTheory = Theory.empty
        .withSort(A)
        .withFunctionDeclaration(relation)



    def AnyClosureEliminator(newCE: ClosureEliminator){

        behavior of "A Closure Eliminator"
        
        it should "be able to connect all points" in {
            val allConnected = Forall(Seq(x.of(A), y.of(A)),
                Term.mkClosure("relation", x, y)
            )
            val newTheory = baseTheory.withAxiom(allConnected)
            Using.resource(ModelFinder.createDefault){ finder => {
                
                finder.setTheory(newTheory)
                finder.setAnalysisScope(A, 4)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}
        }

        it should "treat and empty relation properly" in {
            // No elements in the relation 
            val relIsEmpty = Forall(x.of(A),
                Not(Exists(y.of(A),
                    App("relation", x, y)
                ))
            )
            // Reflexive adds x<->x and nothing else
            val reflexiveOnly = Forall(Seq(x.of(A), y.of(A)),
                Iff(
                    mkReflexiveClosure("relation", x, y),
                    Eq(x,y)
                )
            )
            // Closure remains empty
            val closureAddsNothing = Forall(Seq(x.of(A), y.of(A)),
                Not(mkClosure("relation", x, y))
            )

            val newTheory = baseTheory
                .withAxiom(relIsEmpty)
                .withAxiom(reflexiveOnly)
                .withAxiom(closureAddsNothing)
            Using.resource(ModelFinder.createDefault){ finder => {
                finder.setTheory(newTheory)
                finder.setAnalysisScope(A, 3)
                finder.setTimeout(Seconds(10))
                assert(finder.checkSat() == (ModelFinderResult.Sat)) 
            }}

        }
    }
}