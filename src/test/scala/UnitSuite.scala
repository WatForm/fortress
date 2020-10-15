import org.scalatest._
import org.scalatest.Tag

import fortress.msfol._
import fortress.msfol.DSL._

trait UnitSuite extends FunSuite with Matchers {
    // Give all unit tests MSFOL DSL conversions without explicit imports
    implicit def toDSLTerm(term: Term) = new DSLTerm(term)
    def FunctionSymbol(name: String): FunctionalSymbol = FunctionalSymbol(name)
}

// Test is sensitive to implementation details of the algorithm
object ImplSensitive extends Tag("fortress.tags.ImplSensitive") 

trait CommonFunctionalSymbols extends UnitSuite {
    val f = FunctionSymbol("f")
    val P = FunctionSymbol("P")
    val Q = FunctionSymbol("Q")
    val R = FunctionSymbol("R")
    val S = FunctionSymbol("S")
    val T = FunctionSymbol("T")
}