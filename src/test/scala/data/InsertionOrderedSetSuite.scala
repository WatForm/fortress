import org.scalatest.FunSuite
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.data.InsertionOrderedSet

@RunWith(classOf[JUnitRunner])
class InsertionOrderedSetSuite extends FunSuite {
    
    test("equality with Sets") {
        val s1: Set[Integer] = InsertionOrderedSet.empty
        val s2 = s1 + 5
        val s3 = s2 + 6 + 5 + 6 + 7 + 2 + 1
        
        assert(s1 == Set.empty[String])
        assert(s1 != Set(5))
        assert(s1 != Set(1, 2, 5, 6, 7))
        
        assert(s2 != Set.empty[String])
        assert(s2 == Set(5))
        assert(s2 != Set(1, 2, 5, 6, 7))
        
        assert(s3 != Set.empty[String])
        assert(s3 != Set(5))
        assert(s3 == Set(1, 2, 5, 6, 7))
        
        assert(s1 == s1)
        assert(s1 != s2)
        assert(s1 != s3)
        
        assert(s2 != s1)
        assert(s2 == s2)
        assert(s2 != s3)
        
        assert(s3 != s1)
        assert(s3 != s2)
        assert(s3 == s3)
    }
    
    // TODO rewrite this to use scalacheck
    test("insertion ordered") {
        val set = InsertionOrderedSet.empty[String] + "cat" + "dog" + "mouse" + "rat" + "raccoon" + "bird"
        
        val iter = set.iterator;
        assert(iter.next == "cat")
        assert(iter.next == "dog")
        assert(iter.next == "mouse")
        assert(iter.next == "rat")
        assert(iter.next == "raccoon")
        assert(iter.next == "bird")
        
        val list = set.toList
        
        assert(list == List("cat", "dog", "mouse", "rat", "raccoon", "bird"))
    }
}
