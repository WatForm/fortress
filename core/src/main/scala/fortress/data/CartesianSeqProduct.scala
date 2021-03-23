package fortress.data

import fortress.util.Errors
import java.lang.UnsupportedOperationException


// TODO I suspect this is an efficiency bottleneck

/** Represents the cartesian product of non-empty sequences A_1, ..., A_n, which
 * can be iterated over.
 * For example, if given two sequences A_1 = (a, b, c) and A_2 = (d, e, f),
 * the cartesian product is the sequence ( (a, d), (a, e), (a, f),
 * (b, d), (b, e), (b, f), (c, d), (c, e), (c, f) ).
 * The individual elements of the cartesian product are represented by sequences
 * instead of tuples.
 * IndexedSeq inputs are required for efficiency. The implementation may be able
 * to be improved and this restriction relaxed. */
class CartesianSeqProduct[E](private val sequences: IndexedSeq[IndexedSeq[E]]) extends Iterable[IndexedSeq[E]] {
    
    Errors.Internal.precondition(sequences.forall(_.nonEmpty))
    
    private val numberOfSequences: Int = sequences.size
    
    override def iterator: Iterator[IndexedSeq[E]] = new ProductIterator()
    
    class ProductIterator extends Iterator[IndexedSeq[E]] {
        // Current position within each sequence
        private val currentPosition: Array[Int] = new Array(numberOfSequences)
        private var atEnd: Boolean = false
        
        for(i <- 0 until numberOfSequences) {
            currentPosition(i) = 0
        }
        
        override def hasNext: Boolean = (!atEnd)
        
        override def next(): IndexedSeq[E] = {
            Errors.Internal.precondition(hasNext)
            
            // Get current item of counter, then increment
            
            // Get current item
            val currentProductTuple: IndexedSeq[E] =
                for(i <- 0 until numberOfSequences) yield
                    sequences(i)(currentPosition(i))
            
            // Increment, counter from left to right
            var index = 0
            while(index < numberOfSequences && currentPosition(index) == (sequences(index).size - 1)) {
                currentPosition(index) = 0
                index += 1
            }
            if(index == numberOfSequences) {
                atEnd = true
            } else {
                currentPosition(index) += 1
            }
            
            currentProductTuple
        }
    }
    
}
