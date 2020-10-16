import org.scalatest._

import fortress.util.Maps

class MapsTest extends UnitSuite {
    test("maps with conflict") {
        val map1 = Map(1 -> "cat", 2 -> "dog")
        val map2 = Map(1 -> "dog", 3 -> "sheep")
        
        Maps.noConflict(map1, map2) should be (false)
    }
    
    test("maps no conflict") {
        val map1 = Map(1 -> "cat", 2 -> "dog")
        val map2 = Map(3 -> "sheep")
        val map3 = Map(2 -> "dog", 3 -> "horse")
        
        Maps.noConflict(map1, map2) should be (true)
        Maps.noConflict(map1, map3) should be (true)
    }
    
    test("map merge conflict") {
        val map1 = Map(1 -> "cat", 2 -> "dog")
        val map2 = Map(1 -> "dog", 3 -> "sheep")
        
        an [fortress.util.Errors.Internal.PreconditionError] should be thrownBy {Maps.merge(map1, map2)}
    }
    
    test("map merge no conflict") {
        val map1 = Map(1 -> "cat", 2 -> "dog")
        val map2 = Map(3 -> "sheep")
        val map3 = Map(2 -> "dog", 3 -> "horse")
        
        Maps.merge(map1, map2) should be (Map(1 -> "cat", 2 -> "dog", 3 -> "sheep"))
        Maps.merge(map1, map3) should be (Map(1 -> "cat", 2 -> "dog", 3 -> "horse"))
    }
}
