package fortress.util

object Extensions {
    implicit class IndexedSeqExtension[A](vec: IndexedSeq[A]) {
        def rangeSlice(range: Range): IndexedSeq[A] = for(i <- range) yield vec(i) 
    }
}
