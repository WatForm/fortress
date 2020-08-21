package fortress.util

object Extensions {
    implicit class IndexedSeqExtension[A](vec: IndexedSeq[A]) {
        def rangeSlice(range: Range): IndexedSeq[A] = for(i <- range) yield vec(i) 
    }

    implicit class ListExtension[A](list: List[A]) {
        def interleave(other: List[A]): List[A] = (list, other) match {
            case (x :: xs, y :: ys) => x :: y :: (xs interleave ys)
            case (_, Nil) => list
            case (Nil, _) => other
        }
    }
}
