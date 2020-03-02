package fortress.data

import fortress.util.Errors

/** Mutable data structure maintaining a partition of a set of integers.*/
trait UnionFind {
    
    /** Create a new set and yield a representative. */
    def makeSet(): Int
    
    /** Merge the sets containing a and b. */
    def union(a: Int, b: Int): Unit
    
    /** A representative of the set containing e */
    def find(e: Int): Int
}
