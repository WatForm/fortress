import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.util.StopWatch

@RunWith(classOf[JUnitRunner])
class StopWatchTest extends FunSuite with Matchers {
    
    test("format milliseconds") {
        StopWatch.formatNano(43000000L) should be ("0.043s")
    }
    
    test("format seconds") {
        StopWatch.formatNano(54321000000L) should be ("54.321s")
    }
    
    test("format minutes") {
        StopWatch.formatNano(654321000000L) should be ("10m 54.321s")
    }
    
    test("format hours") {
        StopWatch.formatNano(76543210000000L) should be ("21h 15m 43.210s")
    }
}
