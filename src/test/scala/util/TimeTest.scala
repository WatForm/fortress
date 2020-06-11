import org.scalatest._

import fortress.util._

class TimeTest extends UnitSuite {
    
    test("format milliseconds") {
        Nanoseconds(43000000L).prettyPrint should be ("0.043s")
    }
    
    test("format seconds") {
        Nanoseconds(54321000000L).prettyPrint should be ("54.321s")
    }
    
    test("format minutes") {
        Nanoseconds(654321000000L).prettyPrint should be ("10m 54.321s")
    }
    
    test("format hours") {
        Nanoseconds(76543210000000L).prettyPrint should be ("21h 15m 43.210s")
    }
}
