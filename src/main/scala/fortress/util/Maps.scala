package fortress.util

object Maps {
    def noConflict[A, B](map1: Map[A, B], map2: Map[A, B]) = {
        val commonKeys = map1.keySet.intersect(map2.keySet)
        commonKeys.forall(key => map1(key) == map2(key))
    }
}
