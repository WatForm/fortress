import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.data.IntSuffixNameGenerator

@RunWith(classOf[JUnitRunner])
class NameGeneratorTest extends FunSuite with Matchers {
    
    test("integer suffix name generator") {
        val forbid = Set("sk_3")
        val gen = new IntSuffixNameGenerator(forbid, 2)
        
        gen.freshName("sk") should be ("sk_2")
        gen.freshName("sk") should be ("sk_4")
        gen.freshName("sk") should be ("sk_5")
    }
}
