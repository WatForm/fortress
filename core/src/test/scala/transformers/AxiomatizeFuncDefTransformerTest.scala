import fortress.msfol._
import fortress.transformers._

class AxiomatizeFuncDefTransformerTest extends UnitSuite with CommonSymbols {

    val axiomatize = AxiomatizeFuncDefTransformer

    val baseTheory = Theory.empty
            .withSort(IntSort)
            .withSort(A)

    test("simple functions") {

        val fd1 = FunctionDefinition(
            "max",
            List(AnnotatedVar(Var("x"), IntSort), AnnotatedVar(Var("y"), IntSort)),
            IntSort,
            IfThenElse(BuiltinApp(IntLT, Var("x"), Var("y")), Var("y"), Var("x"))
        )

        val fd2 = FunctionDefinition(
            "power2",
            List(AnnotatedVar(Var("x"), IntSort)),
            BoolSort,
            OrList(Eq(Var("x"), IntegerLiteral(8)), Eq(Var("x"), IntegerLiteral(4)), Eq(Var("x"), IntegerLiteral(2)), Eq(Var("x"), IntegerLiteral(1)))
        )

        val fd3 = FunctionDefinition(
            "AAA",
            List(AnnotatedVar(Var("x"), A)),
            BoolSort,
            Top
        )

        val axiom1 = Forall(
            fd1.argSortedVar, Eq(App(fd1.name, fd1.argSortedVar.map(av => av.variable)), fd1.body)
        )

        val axiom2 = Forall(
            fd2.argSortedVar, Eq(App(fd2.name, fd2.argSortedVar.map(av => av.variable)), fd2.body)
        )

        val axiom3 = Forall(
            fd3.argSortedVar, Eq(App(fd3.name, fd3.argSortedVar.map(av => av.variable)), fd3.body)
        )

        val theory = baseTheory
                .withFunctionDefinitions(fd1, fd2, fd3)

        val expected = baseTheory
                .withFunctionDeclaration(FuncDecl("max", IntSort, IntSort, IntSort))
                .withFunctionDeclaration(FuncDecl("power2", IntSort, BoolSort))
                .withFunctionDeclaration(FuncDecl("AAA", A, BoolSort))
                .withAxiom(axiom1)
                .withAxiom(axiom2)
                .withAxiom(axiom3)

        axiomatize(theory) should be (expected)

    }



}
