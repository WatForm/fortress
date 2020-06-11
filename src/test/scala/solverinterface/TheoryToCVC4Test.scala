import org.scalatest._

import fortress.solverinterface.TheoryToCVC4
import fortress.msfol._
import fortress.msfol.Sort._
import fortress.msfol.Term._
import fortress.msfol.FuncDecl._

class TheoryToCVC4Test extends UnitSuite {
    test("simple theory test") {
        val S = mkSortConst("S")
        val theory: Theory = Theory.empty
            .withSort(S)
            .withConstants(mkVar("x") of S, mkVar("y") of S)
            .withFunctionDeclaration(mkFuncDecl("f", S, S, BoolSort))
            .withAxiom(mkApp("f", mkVar("x"), mkVar("y")))
        
        val converter: TheoryToCVC4 = new TheoryToCVC4(theory)
        converter.sortConversionMap.size should be (2)
        converter.constantConversionMap.size should be (2)
        converter.funcConversionMap.size should be (1)
    }

    test("sort conversion") {
        val theory: Theory = Theory.empty
            .withSorts(BoolSort, IntSort, BitVectorSort(8), BitVectorSort(16), mkSortConst("S"), mkSortConst("T"))
    
        val converter: TheoryToCVC4 = new TheoryToCVC4(theory)
        val sortMap = converter.sortConversionMap
    
        sortMap.size should be (6)
        // The comparison of types only works with equals, not ==
        assert(sortMap.apply(BoolSort) equals converter.em.booleanType)
        assert(sortMap.apply(IntSort) equals converter.em.integerType)
        assert(sortMap.apply(BitVectorSort(8)) equals converter.em.mkBitVectorType(8))
        assert(sortMap.apply(BitVectorSort(16)) equals converter.em.mkBitVectorType(16))
        assert(sortMap.apply(mkSortConst("S")).toString equals "S")
        assert(sortMap.apply(mkSortConst("T")).toString equals "T")
    }
}
