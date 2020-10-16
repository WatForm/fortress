package fortress.util

import fortress.util.Errors

object Maps {
    def noConflict[A, B](map1: Map[A, B], map2: Map[A, B]): Boolean = {
        val commonKeys = map1.keySet.intersect(map2.keySet)
        commonKeys.forall(key => map1(key) == map2(key))
    }

    def findConflict[A, B](map1: Map[A, B], map2: Map[A, B]): Option[A] = {
        val commonKeys = map1.keySet.intersect(map2.keySet)
        commonKeys.find(key => map1(key) != map2(key))
    }
    
    def merge[A, B](map1: Map[A, B], map2: Map[A, B]): Map[A, B] = {
        findConflict(map1, map2) match {
            case None => map1 ++ map2
            case Some(elem) => {
                Errors.Internal.preconditionFailed(s"Map conflict: key: ${elem}, value1: ${map1(elem)}, value2: ${map2(elem)}")
            }
        }
    }
    
    def isInjective[A, B](map: Map[A, B]): Boolean = {
        map.values.toSet.size == map.keySet.size
    }
    
    def isIdentity[A](map: Map[A, A]): Boolean = {
        map.forall{case (x, y) => x == y}
    }

    def removeFixedPoints[A >: Null](map: Map[A, A]): Map[A, A] = {
        Errors.Internal.precondition(map != null)
        Errors.Internal.precondition(!map.keySet.contains(null))
        Errors.Internal.precondition(!map.values.toSet.contains(null))
        map.filter{ case (k, v) => k != v }
    }

    def containsFixedPoint[A](map: Map[A, A]): Boolean = {
        map.exists(pair => pair._1 == pair._2)
    }
}
