import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class NegativeTypeCheckTest extends UnitSuite {
    
    val A = Sort.mkSortConst("A")
    val B = Sort.mkSortConst("B")
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val p = Var("p")
    val q = Var("q")
    
    val P = FuncDecl.mkFuncDecl("P", A, Sort.Bool)
    val Q = FuncDecl.mkFuncDecl("Q", B, Sort.Bool)
    val f = FuncDecl.mkFuncDecl("f", A, B)
    val g = FuncDecl.mkFuncDecl("g", B, A)
    val h = FuncDecl.mkFuncDecl("h", Sort.Bool, Sort.Bool)
    val R = FuncDecl.mkFuncDecl("R", A, A, Sort.Bool)
    val S = FuncDecl.mkFuncDecl("S", A, B, Sort.Bool)
    
    val transitionRelation = FuncDecl.mkFuncDecl("transition", A, A, Sort.Bool)
    val transitionFunction = FuncDecl.mkFuncDecl("transition", A, Sort.Bool)
    
    test("free variable") {
        // A free var should fail typechecking
        val sig = Signature.empty
            .withSort(A)
        
        an [fortress.data.TypeCheckException.UndeterminedSort] should be thrownBy {
            x.typeCheck(sig)
        }
    }
    
    test("function app const wrong arg") {
        // Application of a function to a constant of the wrong argument type
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(g)
        val app = App("g", x)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            app.typeCheck(sig)
        }
    }
    
    test("function app const missing decl") {
        // Use of a function that is missing a declaration
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A))
        val app = App("f", x)
        an [fortress.data.TypeCheckException.UnknownFunction] should be thrownBy {
            app.typeCheck(sig)
        }
    }
    
    test("predicate app forall var wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P)
        val app = Forall(y.of(B), App("P", y))
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            app.typeCheck(sig)
        }
    }
    
    test("predicate app exists var wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P)
        val app = Exists(y.of(B), App("P", y))
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            app.typeCheck(sig)
        }
    }
    
    test("nested app wrong arg 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(g, f, P)
        val fx = App("f", x)
        val ffx = App("f", fx)
        fx.typeCheck(sig).sort should be (B)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            ffx.typeCheck(sig)
        }
    }
    
    test("nested app wrong arg 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(g, f, P)
        val fx = App("f", x)
        val ffx = App("f", fx)
        val pffx = App("P", ffx)
        fx.typeCheck(sig).sort should be (B)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            pffx.typeCheck(sig)
        }
    }
    
    test("and wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(Sort.Bool))
            .withFunctionDeclarations(f)
        val arg1 = App("f", x)
        val arg2 = y
        val and = And(arg1, arg2)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            and.typeCheck(sig)
        }
    }
    
    test("or wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(Sort.Bool))
            .withFunctionDeclarations(f)
        val arg1 = App("f", x)
        val arg2 = y
        val or = Or(arg1, arg2)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            or.typeCheck(sig)
        }
    }
    
    test("imp wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(Sort.Bool))
            .withFunctionDeclarations(f)
        val arg1 = App("f", x)
        val arg2 = y
        val imp = Implication(arg1, arg2)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            imp.typeCheck(sig)
        }
    }
    
    test("distinct wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g)
        val arg1 = App("f", x)
        val arg2 = y
        val arg3 = App("g", App("f", x))
        val distinct = Distinct(arg1, arg2, arg3)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            distinct.typeCheck(sig)
        }
    }
    
    test("eq wrong arg 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g)
        val arg1 = App("f", x)
        val arg2 = y
        val arg3 = App("g", App("f", x))
        val distinct = Distinct(arg1, arg2, arg3)
        val eq1 = Eq(arg1, arg3)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            eq1.typeCheck(sig)
        }
    }
    
    test("eq wrong arg 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g)
        val arg1 = App("f", x)
        val arg2 = y
        val arg3 = App("g", App("f", x))
        val eq2 = Eq(arg2, arg3)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            eq2.typeCheck(sig)
        }
    }
    
    test("not wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(f)
        val not = Not(App("f", x))
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            not.typeCheck(sig)
        }
    }
    
    test("forall wrong arg") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclarations(f, g)
        val forall = Forall(x.of(A), App("f", x))
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            forall.typeCheck(sig)
        }
    }
    
    test("unbound") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
        val forall = Forall(x.of(A), App("Q", y))
        an [fortress.data.TypeCheckException.UndeterminedSort] should be thrownBy {
            forall.typeCheck(sig)
        }
    }
    
    // Check that errors percolate upwards
    test("nested error 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f)
        val bad1 = Or(x, Top)
        val t1 = And(Implication(Not(bad1), Bottom), Top)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t1.typeCheck(sig)
        }
    }
    
    test("nested error 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f)
        val bad2 = App("f", y)
        val t2 = Or(Eq(y, bad2), Top)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t2.typeCheck(sig)
        }
    }
    
    // Former bug
    test("half quantified") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        
        // x is a free variable in the second and argument -- should fail typechecking
        val t = And(
            Forall(x.of(A), App("P", x)),
            App("P", x)
        )
        
        an [fortress.data.TypeCheckException.UndeterminedSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    // Former bug
    test("half quantified multiple") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        
        // x is a free variable in the second and argument -- should fail typechecking
        val t = And(
            Forall(Seq(x.of(A), y.of(A)), App("P", x)),
            App("P", x)
        )
        
        an [fortress.data.TypeCheckException.UndeterminedSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    // Former bug
    test("non existent sort quantifier") {
        val sig = Signature.empty
        val t = Forall(x.of(A), Top)
        an [fortress.data.TypeCheckException.UndeclaredSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    test("function wrong arity") {
        // Application of function to wrong number of arguments
        val sig = Signature.empty
            .withSort(A)
            .withConstantDeclaration(x.of(A))
        val t = App("f", x, x)
        an [fortress.data.TypeCheckException.UnknownFunction] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    test("domain element unknown sort") {
        // Use a domain element of an undeclared type
        val sig = Signature.empty
            .withSorts(A)
        val t = DomainElement(2, B)
        an [fortress.data.TypeCheckException.UndeclaredSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    test("domain element sort bool") {
        // Use a domain element of type Bool
        val sig = Signature.empty
            .withSort(A)
        val t = DomainElement(2, Sort.Bool)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
    test("ite mismatch arg sorts") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of B)
        
        val t = IfThenElse(Top, x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }


    test("closure mismatch arg sort 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of B, y of A)
            .withFunctionDeclarations(R)

        val t = Term.mkClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure mismatch arg sort 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of B)
            .withFunctionDeclarations(R)

        val t = Term.mkClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure unknown function") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x of A, y of A)

        val t = Term.mkClosure("R", x, y)
        an [fortress.data.TypeCheckException.UnknownFunction] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure wrong function sort") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure wrong number of args") {
        val S = FuncDecl.mkFuncDecl("S", A, A, A, Sort.Bool)
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure mismatch function sort 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("closure mismatch function sort 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of B, y of A)
            .withFunctionDeclarations(R)

        val t = Term.mkClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure mismatch arg sort 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of B, y of A)
            .withFunctionDeclarations(R)

        val t = Term.mkReflexiveClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure mismatch arg sort 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of B)
            .withFunctionDeclarations(R)

        val t = Term.mkReflexiveClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure unknown function") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x of A, y of A)

        val t = Term.mkReflexiveClosure("R", x, y)
        an [fortress.data.TypeCheckException.UnknownFunction] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure wrong function sort") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkReflexiveClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure wrong number of args") {
        val S = FuncDecl.mkFuncDecl("S", A, A, A, Sort.Bool)
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkReflexiveClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure mismatch function sort 1") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(S)

        val t = Term.mkReflexiveClosure("S", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }

    test("reflexive closure mismatch function sort 2") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x of B, y of A)
            .withFunctionDeclarations(R)

        val t = Term.mkReflexiveClosure("R", x, y)
        an [fortress.data.TypeCheckException.WrongSort] should be thrownBy {
            t.typeCheck(sig)
        }
    }
    
}
