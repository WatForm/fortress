import org.scalatest._

import fortress.msfol._
import fortress.transformers._

class IntegerToBitVectorTransformerTest extends UnitSuite {
    test("basic literals") {
        val theory = Theory.empty
            .withAxiom(Not(IntegerLiteral(1) === IntegerLiteral(2)))

        val problemState = ProblemState(theory,Map(IntSort -> ExactScope(4)))

        val expected = ProblemState(
            Theory.empty
            .withAxiom(Not(
                BitVectorLiteral(value = 1, bitwidth = 4) === BitVectorLiteral(value = 2, bitwidth = 4))),
            Map.empty
        )

        val transformer = IntegerToBitVectorTransformer
        transformer(problemState) should be (expected)
    }
    
    test("constants") {
        val i = Var("i")
        
        val theory = Theory.empty
            .withConstant(i of IntSort)
            .withAxiom(i === IntegerLiteral(5))

        val problemState = ProblemState(theory,Map(IntSort->ExactScope(4)))

        val expected = ProblemState(
            Theory.empty
            .withConstant(i of BitVectorSort(4))
            .withAxiom(i === BitVectorLiteral(value = 5, bitwidth = 4)),
            Map.empty
        )
        
        val transformer = IntegerToBitVectorTransformer
        transformer(problemState) should be (expected)
    }
    
    test("arithmetic operators") {
        val i = Var("i")
        val j = Var("j")
        
        val theory = Theory.empty
            .withConstants(i of IntSort, j of IntSort)
            .withAxiom(BuiltinApp(IntPlus, i, j) === BuiltinApp(IntPlus, i, j))

        val problemState = ProblemState(theory,Map(IntSort->ExactScope(4)))
        
        val expected = ProblemState(
            Theory.empty
            .withConstants(i of BitVectorSort(4), j of BitVectorSort(4))
            .withAxiom(BuiltinApp(BvPlus, i, j) === BuiltinApp(BvPlus, i, j)),
            Map.empty
        )

        val transformer = IntegerToBitVectorTransformer
        transformer(problemState) should be (expected)
    }
    
    test("functions") {
        val A = SortConst("A")
        val c = Var("c")
        
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(FuncDecl("f", A, IntSort, IntSort))
            .withConstant(c of A)
            .withAxiom(App("f", c, IntegerLiteral(5)) === IntegerLiteral(7))

        val problemState = ProblemState(theory,Map(IntSort->ExactScope(4)))
        
        val expected = ProblemState(
            Theory.empty
            .withSort(A)
            .withFunctionDeclaration(FuncDecl("f", A, BitVectorSort(4), BitVectorSort(4)))
            .withConstant(c of A)
            .withAxiom(App("f", c, BitVectorLiteral(value = 5, bitwidth = 4)) === BitVectorLiteral(value = 7, bitwidth = 4)),
            Map.empty
        )

        val transformer = IntegerToBitVectorTransformer
        transformer(problemState) should be (expected)
    }
    
    test("quantifiers") {
        val x = Var("x")
        val y = Var("y")
        
        val theory = Theory.empty
            .withFunctionDeclaration(FuncDecl("f", IntSort, IntSort, IntSort))
            .withAxiom(Forall( Seq(x of IntSort, y of IntSort), BuiltinApp(IntPlus, x, y) === App("f", x, y)))

        val problemState = ProblemState(theory,Map(IntSort->ExactScope(4)))
        
        val expected = ProblemState(
            Theory.empty
            .withFunctionDeclaration(FuncDecl("f", BitVectorSort(4), BitVectorSort(4), BitVectorSort(4)))
            .withAxiom(Forall( Seq(x of BitVectorSort(4), y of BitVectorSort(4)), BuiltinApp(BvPlus, x, y) === App("f", x, y))),
            Map.empty
        )

        val transformer = IntegerToBitVectorTransformer
        transformer(problemState) should be (expected)
    }
}
