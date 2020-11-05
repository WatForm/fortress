import org.scalatest._

import fortress.data.IntSuffixNameGenerator

class NameGeneratorTest extends UnitSuite {
    
    test("integer suffix name generator") {
        val forbid = Set("sk_3")
        val gen = new IntSuffixNameGenerator(forbid, 2)
        
        gen.freshName("sk") should be ("sk_2")
        gen.freshName("sk") should be ("sk_4")
        gen.freshName("sk") should be ("sk_5")
    }
}
