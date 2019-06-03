package fortress.data

import fortress.util.Errors
import java.lang.UnsupportedOperationException

import scala.collection.immutable.Seq


// TODO I suspect this is an efficiency bottleneck

/** Represents the cartesian product of sequences A_1, ..., A_n.
    IndexedSeq inputs are required for efficiency. The implementation may be able
    to be improved and this restriction relaxed. */
class CartesianSeqProduct[E](private val sequences: IndexedSeq[IndexedSeq[E]]) extends Iterable[Seq[E]] {
    
    Errors.precondition(sequences.forall(_.nonEmpty))
    
    private val numberOfSequences: Int = sequences.size
    
    override def iterator: Iterator[Seq[E]] = new ProductIterator()
    
    class ProductIterator extends Iterator[Seq[E]] {
        // Current position within each sequence
        private val currentPosition: Array[Int] = new Array(numberOfSequences)
        private var atEnd: Boolean = false
        
        for(i <- 0 to numberOfSequences) {
            currentPosition(i) = 0
        }
        
        override def hasNext: Boolean = (!atEnd)
        
        override def next(): Seq[E] = {
            Errors.precondition(hasNext)
            
            // Get current item of counter, then increment
            
            // Get current item
            val currentProductTuple: Seq[E] = {
                // Ugly, but we are doing this for efficiency
                val buffer = new scala.collection.mutable.ListBuffer[E]
                var i = 0
                while(i < numberOfSequences) {
                    buffer += sequences(i)(currentPosition(i))
                    i += 1
                }
                buffer.toList
            }
            
            // Increment, counter from left to right
            var index = 0
            while(index < numberOfSequences && currentPosition(index) == sequences(index).size - 1) {
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
