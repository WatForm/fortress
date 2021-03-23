package fortress.util

import fortress.util.Errors
import fortress.data.CartesianSeqProduct

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

    case class NondeterministicValue[A](possibleValues: Set[A])

    /**
      * A map which for each input, nondeterministically produces an output.
      */
    case class NondeterministicMap[A, B](map: Map[A, NondeterministicValue[B]]) {
        /**
         * Nondeterministically returns a regular map.
         * This regular map represents some choice of how the nondeterministic map could behave when run once on each of its inputs.
         */
        def singleStepMap: NondeterministicValue[Map[A, B]] = {
            val nmapAsSeq: IndexedSeq[(A, NondeterministicValue[B])] = map.toIndexedSeq
            val inputsOrdered: IndexedSeq[A] = nmapAsSeq.map(_._1)
            val outputsOrdered: IndexedSeq[NondeterministicValue[B]] = nmapAsSeq.map(_._2)
            // Generate all possible output combinations from the nondeterministic values
            val allOutputCombinations: IndexedSeq[IndexedSeq[B]] = (new CartesianSeqProduct(outputsOrdered.map(_.possibleValues.toIndexedSeq))).iterator.toIndexedSeq
            val possibleMaps: Seq[Map[A, B]] = for(
                outputCombination <- allOutputCombinations
            ) yield {
                Errors.Internal.assertion(inputsOrdered.size == outputCombination.size)
                val possibleMap: Map[A, B] = (for(i <- (0 until inputsOrdered.size)) yield {inputsOrdered(i) -> outputCombination(i)}).toMap
                possibleMap
            }
            NondeterministicValue(possibleMaps.toSet)
        }
    }

    object NondeterministicMap {
        def fromLists[A, B](map: Map[A, Seq[B]]): NondeterministicMap[A, B] = new NondeterministicMap(for((input, outputSeq) <- map) yield (input -> NondeterministicValue(outputSeq.toSet)))
    }

    
}
