import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.operations.TermOps._

class PositiveTypeCheckTest extends UnitSuite {
    
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
    val next = FuncDecl.mkFuncDecl("next", A, A)
    
    test("constant") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A))
        
        x.typeCheck(sig).sort should be (A)
    }
    
    test("function app const") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(f)
        val app = App("f", x)
        
        app.typeCheck(sig).sort should be (B)
    }
    
    test("predicate app quantified var") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(P)
        val app1 = Forall(x.of(A), App("P", x))
        val app2 = Exists(x.of(A), App("P", x))
        
        app1.typeCheck(sig).sort should be (Sort.Bool)
        app2.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("quantified bool and") {
        val sig = Signature.empty
            .withSorts(A)
            .withFunctionDeclarations(h)
        val term1 = Forall(x.of(Sort.Bool), Or(x, App("h", x)))
        val term2 = Forall(x.of(Sort.Bool), Or(x, App("h", x)))
        
        term1.typeCheck(sig).sort should be (Sort.Bool)
        term2.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("nested app") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(g, f, P)
        val fx = App("f", x)
        val gfx = App("g", fx)
        val pgfx = App("P", gfx)
        
        fx.typeCheck(sig).sort should be (B)
        gfx.typeCheck(sig).sort should be (A)
        pgfx.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("and, or, imp") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(y.of(Sort.Bool))
            .withFunctionDeclarations(P)
        val arg1 = Forall(x.of(A), App("P", x))
        val arg2 = y
        val and = And(arg1, arg2)
        val or = Or(arg1, arg2)
        val imp = Implication(arg1, arg2)
        and.typeCheck(sig).sort should be (Sort.Bool)
        or.typeCheck(sig).sort should be (Sort.Bool)
        imp.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    
    test("eq, distinct") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g)
        val arg1 = App("f", x)
        val arg2 = y
        val arg3 = App("f", App("g", App("f", x)))
        val distinct = Distinct(arg1, arg2, arg3)
        val eq1 = Eq(arg1, arg2)
        val eq2 = Eq(arg1, arg3)
        val eq3 = Eq(arg2, arg3)
        distinct.typeCheck(sig).sort should be (Sort.Bool)
        eq1.typeCheck(sig).sort should be (Sort.Bool)
        eq2.typeCheck(sig).sort should be (Sort.Bool)
        eq3.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("top, bottom") {
        val sig = Signature.empty
        Top.typeCheck(sig).sort should be (Sort.Bool)
        Bottom.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("not") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(P)
        val not = Not(App("P", x))
        not.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("quantifier") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclarations(P, Q)
        val forall = Forall(x.of(A), App("P", x))
        val exists = Exists(y.of(B), App("Q", y))
        forall.typeCheck(sig).sort should be (Sort.Bool)
        exists.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("quantifier shadow") {
        val sig = Signature.empty
            .withSorts(A, B)
            .withConstantDeclarations(x.of(B), y.of(A))
            .withFunctionDeclarations(P, Q)
        val forall = Forall(x.of(A), App("P", x))
        val exists = Exists(y.of(B), App("Q", y))
        forall.typeCheck(sig).sort should be (Sort.Bool)
        exists.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("half quantified but constant") {
        val sig = Signature.empty
            .withSorts(A)
            .withConstantDeclarations(x.of(A))
            .withFunctionDeclarations(P)
        
        // x is free in the second and argument -- but it is a constant so this is fine
        val t = And(
            Forall(x.of(A), App("P", x)),
            App("P", x)
        )
        
        t.typeCheck(sig).sort should be (Sort.Bool)
    }
    
    test("domainElement") {
        val sig = Signature.empty
            .withSort(A)
        
        val t = DomainElement(2, A)
        
        t.typeCheck(sig).sort should be (A)
    }
    
    test("ite") {
        val sig = Signature.empty
            .withSort(A)
            .withConstantDeclarations(x of A, y of A)
        
        val t = IfThenElse(x === y, x, y)
        t.typeCheck(sig).sort should be (A)
    }
    
    test("setcardinality"){
        val sig = Signature.empty 
            .withSort(A)
            .withConstantDeclarations(x of A, y of A)
            .withFunctionDeclarations(P)
            
        val t = SetCardinality(P.name)
        t.typeCheck(sig).sort should be (Sort.Bool)
    }


    test("closure") {
        val sig = Signature.empty
            .withSort(A)
            .withFunctionDeclarations(R)
            .withConstantDeclarations(x of A, y of A)

        val t = Term.mkClosure("R", x, y)
        t.typeCheck(sig).sort should be (Sort.Bool)
    }

    test("reflexiveClosure") {
        val sig = Signature.empty
            .withSort(A)
            .withFunctionDeclarations(R)
            .withConstantDeclarations(x of A, y of A)

        val t = Term.mkReflexiveClosure("R", x, y)
        t.typeCheck(sig).sort should be (Sort.Bool)
    }
        
}
