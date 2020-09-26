import org.scalatest._
import org.scalatest.Tag

abstract class UnitSuite extends FunSuite with Matchers

// Test is sensitive to implementation details of the algorithm
object ImplSensitive extends Tag("fortress.tags.ImplSensitive") 
