import org.scalatest._

import fortress.data._

class SimpleUnionFindTest extends UnitSuite {
    test("simple union find") {
        val uf = new SimpleUnionFind
        
        uf.find(1) should be (1)
        uf.find(2) should be (2)
        uf.find(0) should be (0)
        uf.find(5) should be (5)
        
        uf.union(1, 2)
        uf.union(2, 5)
        
        val rep = uf.find(2)
        Seq(1, 2, 5) should contain (rep)
        uf.find(1) should be (rep)
        uf.find(2) should be (rep)
        uf.find(5) should be (rep)
        
        uf.find(0) should be (0)
        uf.find(4) should be (4)
    }
}
