import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class IntToBVTransformerTests extends UnitSuite {
    test("basic literals") {
        val theory = Theory.empty
            .withAxiom(Not(IntegerLiteral(1) === IntegerLiteral(2)))

        val problemState = ProblemState(theory).withScopes(Map(IntSort -> ExactScope(16)))

        val expected = ProblemState(
            Theory.empty
                .withAxiom(Not(
                    BitVectorLiteral(value = 1, bitwidth = 4) === BitVectorLiteral(value = 2, bitwidth = 4))))
            .withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))

        val transformer = IntToBVTransformer
        val result = transformer(problemState).withoutUnapplyInterps()
        result should be (expected)
    }
    
    test("constants") {
        val i = Var("i")
        
        val theory = Theory.empty
            .withConstantDeclaration(i of IntSort)
            .withAxiom(i === IntegerLiteral(5))

        val problemState = ProblemState(theory).withScopes(Map(IntSort->ExactScope(16)))

        val expected = ProblemState(
            Theory.empty
                .withConstantDeclaration(i of BitVectorSort(4))
                .withAxiom(i === BitVectorLiteral(value = 5, bitwidth = 4)))
            .withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))
        
        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }
    
    test("arithmetic operators") {
        val i = Var("i")
        val j = Var("j")
        
        val theory = Theory.empty
            .withConstantDeclarations(i of IntSort, j of IntSort)
            .withAxiom(BuiltinApp(IntPlus, i, j) === BuiltinApp(IntPlus, i, j))

        val problemState = ProblemState(theory).withScopes(Map(IntSort->ExactScope(16)))
        
        val expected = ProblemState(
            Theory.empty
                .withConstantDeclarations(i of BitVectorSort(4), j of BitVectorSort(4))
                .withAxiom(BuiltinApp(BvPlus, i, j) === BuiltinApp(BvPlus, i, j))).
            withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))

        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }
    
    test("functions") {
        val A = SortConst("A")
        val c = Var("c")
        
        val theory = Theory.empty
            .withSort(A)
            .withFunctionDeclaration(FuncDecl("f", A, IntSort, IntSort))
            .withConstantDeclaration(c of A)
            .withAxiom(App("f", c, IntegerLiteral(5)) === IntegerLiteral(7))

        val problemState = ProblemState(theory).withScopes(Map(IntSort->ExactScope(16)))
        
        val expected = ProblemState(
            Theory.empty
                .withSort(A)
                .withFunctionDeclaration(FuncDecl("f", A, BitVectorSort(4), BitVectorSort(4)))
                .withConstantDeclaration(c of A)
                .withAxiom(App("f", c, BitVectorLiteral(value = 5, bitwidth = 4)) === BitVectorLiteral(value = 7, bitwidth = 4))).
            withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))

        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }
    
    test("quantifiers") {
        val x = Var("x")
        val y = Var("y")
        
        val theory = Theory.empty
            .withFunctionDeclaration(FuncDecl("f", IntSort, IntSort, IntSort))
            .withAxiom(Forall( Seq(x of IntSort, y of IntSort), BuiltinApp(IntPlus, x, y) === App("f", x, y)))

        val problemState = ProblemState(theory).withScopes(Map(IntSort->ExactScope(16)))
        
        val expected = ProblemState(
            Theory.empty
                .withFunctionDeclaration(FuncDecl("f", BitVectorSort(4), BitVectorSort(4), BitVectorSort(4)))
                .withAxiom(Forall( Seq(x of BitVectorSort(4), y of BitVectorSort(4)), BuiltinApp(BvPlus, x, y) === App("f", x, y))))
            .withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))


        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }

    // NAD 2024-05-15 This test used to contain UnBoundedIntSort
    test("IntSort") {
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        val t = Var("t")

        val axiom1: Term = Forall( Seq(z of IntSort, t of IntSort), BuiltinApp(IntPlus, z, t) === App("g", z, t))
        axiom1.isLia = true

        val theory = Theory.empty
                .withFunctionDeclaration(FuncDecl("f", IntSort, IntSort, IntSort))
                .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort, IntSort))
                .withAxiom(Forall( Seq(x of IntSort, y of IntSort), BuiltinApp(IntPlus, x, y) === App("f", x, y)))
                .withAxiom(axiom1)

        val problemState = ProblemState(theory).withScopes(Map(IntSort->ExactScope(16)))

        val expected = ProblemState(
            Theory.empty
                    .withFunctionDeclaration(FuncDecl("f", BitVectorSort(4), BitVectorSort(4), BitVectorSort(4)))
                    .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort, IntSort))
                    .withAxiom(Forall( Seq(x of BitVectorSort(4), y of BitVectorSort(4)), BuiltinApp(BvPlus, x, y) === App("f", x, y)))
                    .withAxiom(axiom1))
            .withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))

        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }

    // this used to contain a bounded int
    test("BoundedIntSort"){
        val theory = Theory.empty
            .withAxiom(Not(IntegerLiteral(1) === IntegerLiteral(2)))

        val problemState = ProblemState(theory)
            .withScopes(Map.empty + (IntSort -> ExactScope(16)))

        val expected = ProblemState(
            Theory.empty
                .withAxiom(Not(
                    BitVectorLiteral(value = 1, bitwidth = 4) === BitVectorLiteral(value = 2, bitwidth = 4))))
            .withScopes(Map.empty + (BitVectorSort(4) -> ExactScope(16)))

        val transformer = IntToBVTransformer
        transformer(problemState).withoutUnapplyInterps() should be (expected)
    }
}
