import org.scalatest._

import fortress.data.CartesianSeqProduct

class CartesianSeqProductTest extends UnitSuite {

    test("ordering") {
        val l1 = IndexedSeq("a", "b", "c")
        val l2 = IndexedSeq("d", "e", "f")

        val product = new CartesianSeqProduct[String](IndexedSeq(l1, l2))

        product.toList should be (List(
            Seq("a", "d"), Seq("b", "d"), Seq("c", "d"), Seq("a", "e"),
            Seq("b", "e"), Seq("c", "e"), Seq("a", "f"), Seq("b", "f"), Seq("c", "f")  
        ))
    }
    
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
    
    test("for each") {
        val l1 = IndexedSeq(1, 2, 3)
        val l2 = IndexedSeq(4, 5)
        val l3 = IndexedSeq(6)
        val l4 = IndexedSeq(7, 8)
        
        val product = new CartesianSeqProduct[Int](IndexedSeq(l1, l2, l3, l4))
        
        val enumeration: Seq[Seq[Int]] = {
            val buffer = new scala.collection.mutable.ListBuffer[Seq[Int]]
            product.foreach(productTuple => buffer += productTuple)
            buffer.toList
        }
        enumeration should be (Seq(
            Seq(1, 4, 6, 7),
            Seq(2, 4, 6, 7),
            Seq(3, 4, 6, 7),
            Seq(1, 5, 6, 7),
            Seq(2, 5, 6, 7),
            Seq(3, 5, 6, 7),
            Seq(1, 4, 6, 8),
            Seq(2, 4, 6, 8),
            Seq(3, 4, 6, 8),
            Seq(1, 5, 6, 8),
            Seq(2, 5, 6, 8),
            Seq(3, 5, 6, 8)
        ))
    }
}
