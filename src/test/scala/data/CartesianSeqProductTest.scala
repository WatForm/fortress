import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.data.CartesianSeqProduct

@RunWith(classOf[JUnitRunner])
class CartesianProductTest extends FunSuite with Matchers{
    
    test("iteration") {
        val l1 = IndexedSeq(1, 2, 3)
        val l2 = IndexedSeq(4, 5)
        val l3 = IndexedSeq(6)
        val l4 = IndexedSeq(7, 8)
        
        val product = new CartesianSeqProduct[Int](IndexedSeq(l1, l2, l3, l4))
        
        val iterator = product.iterator
        iterator.hasNext should be (true)
        iterator.next should be (Seq(1, 4, 6, 7))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(2, 4, 6, 7))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(3, 4, 6, 7))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(1, 5, 6, 7))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(2, 5, 6, 7))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(3, 5, 6, 7))
        iterator.hasNext should be (true)
        
        iterator.next should be (Seq(1, 4, 6, 8))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(2, 4, 6, 8))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(3, 4, 6, 8))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(1, 5, 6, 8))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(2, 5, 6, 8))
        iterator.hasNext should be (true)
        iterator.next should be (Seq(3, 5, 6, 8))
        iterator.hasNext should be (false)
    }
}
