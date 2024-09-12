import fortress.msfol._
import fortress.operations.MaxAlphaRenaming

class MaxAlphaRenamingTest extends UnitSuite {

    test("rename with bound variable shadowing bound variable") {
        val x = Var("x")
        val sort = SortConst("Sort")
        val term = Forall(x of sort, And(Exists(x of sort, App("f", x)), App("g", x)))
        val theory = Theory.empty
            .withSort(sort)
            .withAxiom(term)

        val x0 = Var("x_0")
        val x1 = Var("x_1")
        val expectedTerm = Forall(x0 of sort, And(Exists(x1 of sort, App("f", x1)), App("g", x0)))

        val resultTheory = MaxAlphaRenaming.rename(theory)
        resultTheory.axioms should contain(expectedTerm)
    }

    test("rename with bound variable shadowing constant") {
        val x = Var("x")
        val sort = SortConst("Sort")
        val term = Forall(x of sort, App("f", x))
        val theory = Theory.empty
            .withSort(sort)
            .withConstantDeclaration(x of sort)
            .withAxiom(term)
            .withAxiom(App("g", x)) // use the constant

        val x0 = Var("x_0")
        val expectedTerm = Forall(x0 of sort, App("f", x0))
        val expectedTheory = Theory.empty
            .withSort(sort)
            .withConstantDeclaration(x of sort)
            .withAxiom(expectedTerm)
            .withAxiom(App("g", x))

        val resultTheory = MaxAlphaRenaming.rename(theory)
        resultTheory should equal(expectedTheory)
    }

    test("rename with function definition param shadowing constant") {
        val x = Var("x")
        val sort = SortConst("Sort")
        val funcDefn = FunctionDefinition("f", Seq(x of sort), sort, x)
        val theory = Theory.empty
            .withSort(sort)
            .withConstantDeclaration(x of sort)
            .withFunctionDefinition(funcDefn)
            .withAxiom(App("f", x))

        val x0 = Var("x_0")
        val expectedFuncDefn = FunctionDefinition("f", Seq(x0 of sort), sort, x0)
        val expectedTheory = Theory.empty
            .withSort(sort)
            .withConstantDeclaration(x of sort)
            .withFunctionDefinition(expectedFuncDefn)
            .withAxiom(App("f", x))

        val resultTheory = MaxAlphaRenaming.rename(theory)
        resultTheory should equal(expectedTheory)
    }

}
