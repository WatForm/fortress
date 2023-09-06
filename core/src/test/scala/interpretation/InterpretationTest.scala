import fortress.msfol._
import org.scalatest._
import scala.util.Using
import fortress.interpretation._

class InterpretationTest extends UnitSuite {
    test("Interpret Negative BV") {
        val interp = BasicInterpretation.empty

        for (x <- (-8 until 7)){
            val bv = BitVectorLiteral(x, 4)
            val argSeq = Seq(bv)

            val result = interp.evaluateBuiltIn(CastBVToInt, argSeq)
            result should be (IntegerLiteral(x))
        }
    }

}