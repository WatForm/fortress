package fortress.data

/** An immutable set that is iterated over in insertion order. */
class InsertionOrderedSet[E](
    private val implSet: Set[E],
    private val implVector: Vector[E]
) extends scala.collection.immutable.Set[E] {
    
    // Members declared in scala.collection.GenSetLike
    override def iterator: Iterator[E] = implVector.iterator

    // Members declared in scala.collection.SetLike
    def excl(elem: E): scala.collection.immutable.Set[E] = new InsertionOrderedSet(
        implSet excl elem,
        implVector diff Vector(elem)
    )
    
    def incl(elem: E): InsertionOrderedSet[E] = 
        if(contains(elem)) this
        else new InsertionOrderedSet(implSet + elem, implVector :+ elem)
        
    def contains(elem: E): Boolean = implSet.contains(elem)

}

object InsertionOrderedSet {
    
    // Empty InsertionOrderedSet.
    def empty[T]: InsertionOrderedSet[T] = new InsertionOrderedSet(Set.empty, Vector.empty)
    
    // Generate an InsertionOrderedSet from a Sequence.
    def fromSeq[T](seq: Seq[T]): InsertionOrderedSet[T] = seq.foldLeft(empty[T])((set, elem) => set incl elem)
}
