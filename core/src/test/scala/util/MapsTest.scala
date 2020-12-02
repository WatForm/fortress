import org.scalatest._

import fortress.util.Maps
import fortress.util.Maps._

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

    test("nondeterministic map single step") {
        val map = Map("cat" -> NondeterministicValue(Set(1, 2, 3)), "dog" -> NondeterministicValue(Set(4, 5, 6)))
        val nmap = NondeterministicMap(map)

        val expected: NondeterministicValue[Map[String, Int]] = NondeterministicValue(Set(
            Map("cat" -> 1, "dog" -> 4),
            Map("cat" -> 1, "dog" -> 5),
            Map("cat" -> 1, "dog" -> 6),
            Map("cat" -> 2, "dog" -> 4),
            Map("cat" -> 2, "dog" -> 5),
            Map("cat" -> 2, "dog" -> 6),
            Map("cat" -> 3, "dog" -> 4),
            Map("cat" -> 3, "dog" -> 5),
            Map("cat" -> 3, "dog" -> 6)
        ))

        nmap.singleStepMap should be (expected)
    }
}
