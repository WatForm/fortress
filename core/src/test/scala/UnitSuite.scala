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
    val g = FunctionSymbol("g")
    val P = FunctionSymbol("P")
    val Q = FunctionSymbol("Q")
    val R = FunctionSymbol("R")
    val S = FunctionSymbol("S")
    val T = FunctionSymbol("T")
}

trait CommonVariableSymbols extends UnitSuite {
    val p = Var("p")
    val q = Var("q")
    val w = Var("w")
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val x1 = Var("x1")
    val x2 = Var("x2")
    val x3 = Var("x3")
    val x4 = Var("x4")
}

trait CommonSortSymbols extends UnitSuite {
    val A = SortConst("A")
    val B = SortConst("B")
    val C = SortConst("C")
    val D = SortConst("D")
}

trait CommonSymbols extends UnitSuite with CommonFunctionalSymbols with CommonVariableSymbols with CommonSortSymbols