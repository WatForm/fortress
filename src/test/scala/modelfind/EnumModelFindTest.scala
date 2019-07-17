import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import scala.collection.immutable.Seq

import fortress.msfol._
import fortress.modelfind._

@RunWith(classOf[JUnitRunner])
class EnumModelFindTest extends FunSuite with Matchers {
    
    test("simple enum theory") {
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
            .withAxiom(App("next", green) === yellow)
            .withAxiom(App("next", yellow) === red)
            .withAxiom(App("next", red) === green)
            .withAxiom(c === App("next", red))
        
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        // Do not need to set scope of enum sort
        
        finder.checkSat should be (ModelFinderResult.Sat)
        
        val model = finder.viewModel()
        model.constantInterpretations should be (Map( (c of Colour) -> green) )
        model.sortInterpretations should be (Map( Colour -> Seq(red, yellow, green), BoolSort -> Seq(Term.mkTop, Term.mkBottom)))
        model.functionInterpretations should be (Map(
            next -> Map(
                Seq(red) -> green,
                Seq(yellow) -> red,
                Seq(green) -> yellow
            )
        ))
    }
}
    
