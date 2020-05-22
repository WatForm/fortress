import org.scalatest._

import fortress.util.StopWatch

class StopWatchTest extends UnitSuite {
    
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
