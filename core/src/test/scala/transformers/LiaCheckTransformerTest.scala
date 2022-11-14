import org.scalatest._
import fortress.msfol._
import fortress.problemstate._
import fortress.transformers._

class LiaCheckTransformerTest extends UnitSuite {

    val i = Var("i")
    val j = Var("j")
    val k = Var("k")

    val f = FuncDecl("f", IntSort, IntSort)
    val g = FuncDecl("g", IntSort, IntSort)
    val h = FuncDecl("h", IntSort, IntSort)


    test("simple plus&sub") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withAxiom(BuiltinApp(IntPlus, App("f", i), IntegerLiteral(1)))
                .withAxiom(BuiltinApp(IntSub, App("g", j), IntegerLiteral(2)))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val expect = ProblemState(
            Theory.empty
                    .withConstant(i of UnBoundedIntSort)
                    .withConstant(j of UnBoundedIntSort)
                    .withFunctionDeclaration(FuncDecl("f", UnBoundedIntSort, UnBoundedIntSort))
                    .withFunctionDeclaration(FuncDecl("g", UnBoundedIntSort, UnBoundedIntSort))
                    .withAxiom(BuiltinApp(IntPlus, App("f", i), IntegerLiteral(1)))
                    .withAxiom(BuiltinApp(IntSub, App("g", j), IntegerLiteral(2))),
            Map(IntSort->ExactScope(5))
        )

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (expect)
    }

    test("IntDiv is not lia") {

        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withFunctionDeclaration(f)
                .withAxiom(BuiltinApp(IntDiv, App("f", i), IntegerLiteral(1)))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))


        val transformer = LiaCheckTransformer
        transformer(problemState) should be (problemState)
    }

    test("IntMult") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withAxiom(BuiltinApp(IntMult, App("f", i), IntegerLiteral(1)))
                .withAxiom(BuiltinApp(IntMult, App("g", j), App("g", IntegerLiteral(1))))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val expect = ProblemState(
            Theory.empty
                    .withConstant(i of UnBoundedIntSort)
                    .withConstant(j of IntSort)
                    .withFunctionDeclaration(FuncDecl("f", UnBoundedIntSort, UnBoundedIntSort))
                    .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort))
                    .withAxiom(BuiltinApp(IntMult, App("f", i), IntegerLiteral(1)))
                    .withAxiom(BuiltinApp(IntMult, App("g", j), App("g", IntegerLiteral(1)))),
            Map(IntSort->ExactScope(5))
        )

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (expect)
    }

    test("AndList test") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withAxiom( And(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                .withAxiom( And(Eq(App("g", j), BuiltinApp(IntMult, j, j) ) ,Bottom ) )

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val expect = ProblemState(
            Theory.empty
                    .withConstant(i of UnBoundedIntSort)
                    .withConstant(j of IntSort)
                    .withFunctionDeclaration(FuncDecl("f", UnBoundedIntSort, UnBoundedIntSort))
                    .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort))
                    .withAxiom( And(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                    .withAxiom( And(Eq(App("g", j), BuiltinApp(IntMult, j, j) ) ,Bottom ) ),
            Map(IntSort->ExactScope(5))
        )

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (expect)
    }

    test("OrList test") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withAxiom( Or(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                .withAxiom( Or(Eq(App("g", j), BuiltinApp(IntMult, j, j) ) ,Bottom ) )

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val expect = ProblemState(
            Theory.empty
                    .withConstant(i of UnBoundedIntSort)
                    .withConstant(j of IntSort)
                    .withFunctionDeclaration(FuncDecl("f", UnBoundedIntSort, UnBoundedIntSort))
                    .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort))
                    .withAxiom( Or(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                    .withAxiom( Or(Eq(App("g", j), BuiltinApp(IntMult, j, j) ) ,Bottom ) ),
            Map(IntSort->ExactScope(5))
        )

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (expect)
    }

    test("test-0") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withAxiom( Or(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                .withAxiom( And(Eq(App("g", i), BuiltinApp(IntMult, j, j) ) ,Bottom ) )

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (problemState)
    }

    test("test 1") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withConstant(k of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withFunctionDeclaration(h)
                .withAxiom( Or(Eq(App("f", i), IntegerLiteral(1) ) ,Top ) )
                .withAxiom( And(Eq(App("g", k), BuiltinApp(IntMult, j, j) ) ,Bottom ) )
                .withAxiom( Not(Eq(App("h", k), i)))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (problemState)
    }

    test("test 2") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withConstant(k of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withFunctionDeclaration(h)
                .withAxiom(BuiltinApp(IntMult, App("f", i), IntegerLiteral(1)))
                .withAxiom(BuiltinApp(IntMult, App("g", j), App("g", IntegerLiteral(1))))
                .withAxiom(BuiltinApp(IntMult, App("h", k), IntegerLiteral(2)))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val expect = ProblemState(
            Theory.empty
                    .withConstant(i of UnBoundedIntSort)
                    .withConstant(j of IntSort)
                    .withConstant(k of UnBoundedIntSort)
                    .withFunctionDeclaration(FuncDecl("f", UnBoundedIntSort, UnBoundedIntSort))
                    .withFunctionDeclaration(FuncDecl("g", IntSort, IntSort))
                    .withFunctionDeclaration(FuncDecl("h", UnBoundedIntSort, UnBoundedIntSort))
                    .withAxiom(BuiltinApp(IntMult, App("f", i), IntegerLiteral(1)))
                    .withAxiom(BuiltinApp(IntMult, App("g", j), App("g", IntegerLiteral(1))))
                    .withAxiom(BuiltinApp(IntMult, App("h", k), IntegerLiteral(2))),
            Map(IntSort->ExactScope(5))
        )

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (expect)
    }

    test("test 3") {
        val theory = Theory.empty
                .withConstant(i of IntSort)
                .withConstant(j of IntSort)
                .withConstant(k of IntSort)
                .withFunctionDeclaration(f)
                .withFunctionDeclaration(g)
                .withFunctionDeclaration(FuncDecl("h", IntSort, IntSort, IntSort))
                .withAxiom(BuiltinApp(IntPlus, App("f", i), App("f", k)))
                .withAxiom(BuiltinApp(IntSub, App("g", k), j ))
                .withAxiom(BuiltinApp(IntMult, App("h", i), i))

        val problemState = ProblemState(theory, Map(IntSort->ExactScope(5)))

        val transformer = LiaCheckTransformer
        transformer(problemState) should be (problemState)
    }


}