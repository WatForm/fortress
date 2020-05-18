package fortress.data

import scala.collection.mutable

// Uses O(n) space where n is the size of the maximum integers on which
// union or find is called.
class SimpleUnionFind extends UnionFind {
    
    private val label = mutable.ArrayBuffer.empty[Int]
    
    // The current maximum elements
    // The array has indices 0, 1, ..., n
    private var maxElem = -1
    
    // Expand the collection of integers up to a
    // Each new element is in its own set
    private def expandTo(a: Int): Unit = {
        for(i <- (maxElem + 1) to a) {
            label += i // Label i with itself
        }
    }
    
    override def union(a: Int, b: Int): Unit = {
        expandTo(a)
        expandTo(b)
        if(label(a) != label(b)) {
            // a keeps its label
            // Everything with the label of b changes
            // We have to remember the label of b
            val temp = label(b)
            for(i <- 0 to maxElem) {
                if(temp == label(i)) {
                    label(i) = label(a)
                }
            }
        }
    }
    
    override def find(e: Int): Int = {
        expandTo(e)
        label(e)
    }
}