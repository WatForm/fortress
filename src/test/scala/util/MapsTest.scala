import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.util.Maps

@RunWith(classOf[JUnitRunner])
class MapsTest extends FunSuite with Matchers {
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
        
        an [fortress.util.Errors.PreconditionException] should be thrownBy {Maps.merge(map1, map2)}
    }
    
    test("map merge no conflict") {
        val map1 = Map(1 -> "cat", 2 -> "dog")
        val map2 = Map(3 -> "sheep")
        val map3 = Map(2 -> "dog", 3 -> "horse")
        
        Maps.merge(map1, map2) should be (Map(1 -> "cat", 2 -> "dog", 3 -> "sheep"))
        Maps.merge(map1, map3) should be (Map(1 -> "cat", 2 -> "dog", 3 -> "horse"))
    }
}
