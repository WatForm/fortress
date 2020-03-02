package fortress.data

import scala.collection.mutable

class SimpleUnionFind extends UnionFind {
    
    private val label = mutable.ArrayBuffer.empty[Int]
    private def n = label.size
    
    override def makeSet(): Int = {
        // The new element is the representative of that set.
        val newElem = label.size
        label += newElem
        newElem
    }
    
    override def union(a: Int, b: Int): Unit = {
        if(label(a) != label(b)) {
            // a keeps its label
            // Everything with the label of b changes
            // We have to remember the label of b
            val temp = label(b)
            for(i <- 0 to (n - 1)) {
                if(temp == label(i)) {
                    label(i) = label(a)
                }
            }
        }
    }
    
    override def find(e: Int): Int = {
        label(e)
    }
}
