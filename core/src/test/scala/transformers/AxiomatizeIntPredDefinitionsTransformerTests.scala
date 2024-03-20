import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class AxiomatizeIntPredDefinitionsTransformerTests extends UnitSuite {
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val i = Var("i")
    val j = Var("j")
    val k = Var("k")

    val A = SortConst("A")

    val transformer = AxiomatizeIntPredDefinitionsTransformer

    val baseTheory = Theory.empty
        .withConstantDeclarations(i of IntSort, j of IntSort, k of IntSort)

    val bitwidth = 8
    val bvSort = BitVectorSort(bitwidth)
    val baseTheoryBv = Theory.empty
        .withConstantDeclarations(i of bvSort, j of bvSort, k of bvSort)
    

    def checkTransform(input: Theory, expected: Theory) = {
        val ps = ProblemState(input)
        transformer(ps).theory should equal (expected)
    }

    test("does not change simple function"){
        val theory = baseTheory
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of IntSort),
                    IntSort,
                    BuiltinApp(IntPlus, x, i)
                ))
        checkTransform(theory, theory)
    }

    test("does not change simple function bv"){
        val theory = baseTheoryBv
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of bvSort),
                    bvSort,
                    BuiltinApp(BvPlus, x, i)
                ))
        checkTransform(theory, theory)
    }

    test("changes simple pred"){
        val body = Eq(BuiltinApp(IntPlus, x, i), j)

        val theory = baseTheory
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of IntSort),
                    BoolSort,
                    body
                ))
        
        val expectedTheory = baseTheory
            .withFunctionDeclaration(FuncDecl("f", IntSort, BoolSort))
            .withAxiom(Forall(x of IntSort, Eq(App("f", x), body)))
        checkTransform(theory, expectedTheory)
    }

    test("changes simple pred bv"){
        val body = Eq(BuiltinApp(BvPlus, x, i), j)

        val theory = baseTheory
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of bvSort),
                    BoolSort,
                    body
                ))
        
        val expectedTheory = baseTheory
            .withFunctionDeclaration(FuncDecl("f", bvSort, BoolSort))
            .withAxiom(Forall(x of bvSort, Eq(App("f", x), body)))
        checkTransform(theory, expectedTheory)
    }

    test("does not change ite func"){
        val theory = baseTheory
        .withSort(A)
        .withConstantDeclarations(y of A, z of A)
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of IntSort),
                    IntSort,
                    IfThenElse(Eq(y, z), BuiltinApp(IntPlus, x, i), x)
                ))
        checkTransform(theory, theory)
    }

    test("does not change ite func bv"){
        val theory = baseTheory
        .withSort(A)
        .withConstantDeclarations(y of A, z of A)
            .withFunctionDefinition(
                FunctionDefinition("f",
                    Seq(x of bvSort),
                    bvSort,
                    IfThenElse(Eq(y, z), BuiltinApp(BvPlus, x, i), x)
                ))
        checkTransform(theory, theory)
    }



}