package fortress.data

/** An immutable set that is iterated over in insertion order. */
class InsertionOrderedSet[E](
    private val implSet: Set[E],
    private val implQueue: scala.collection.immutable.Queue[E]
) extends scala.collection.immutable.Set[E] {
    
    // Members declared in scala.collection.GenSetLike
    override def iterator: Iterator[E] = implQueue.iterator

    // Members declared in scala.collection.SetLike
    def -(elem: E): scala.collection.immutable.Set[E] = 
        throw new java.lang.UnsupportedOperationException("InsertionOrderedSet[E] does not support the - operation");
        
    def +(elem: E): InsertionOrderedSet[E] = 
        if(contains(elem)) this
        else new InsertionOrderedSet(implSet + elem, implQueue :+ elem)
        
    def contains(elem: E): Boolean = implSet.contains(elem)

}

object InsertionOrderedSet {
    
    // Empty InsertionOrderedSet.
    def empty[T]: InsertionOrderedSet[T] = new InsertionOrderedSet(Set.empty, scala.collection.immutable.Queue.empty)
    
    // Generate an InsertionOrderedSet from a Sequence.
    def fromSeq[T](seq: Seq[T]): InsertionOrderedSet[T] = seq.foldLeft(empty[T])((set, elem) => set + elem)
}
