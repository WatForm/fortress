import org.scalatest._

import fortress.msfol._
import fortress.operations._
import fortress.data.TypeCheckException

class TypeCheckerTest extends UnitSuite {

    val A = Sort.mkSortConst("A");
    val B = Sort.mkSortConst("B");
    val C = Sort.mkSortConst("C");

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val h = Var("h");
    val j = Var("j");
    val k = Var("k");

    test("Function definition"){
        val fdef = FunctionDefinition("f", Seq(x.of(A), y.of(B)), C, 
            z // the body just returns some constant z
        )
        val sig = Signature.empty
            .withSorts(A,B,C)
            .withFunctionDefinition(fdef)
            .withConstantDeclarations(h.of(A), j.of(B), z.of(C))
        
        val checker = new TypeChecker(sig)
        val application = App("f", Seq(h, j))
        val result = checker.visit(application)

        result.sanitizedTerm should be (application)
        result.sort should be (C)
        result.containsConnectives should be (false)
        result.containsQuantifiers should be (false)
    }

    test("Function declaration") {
        val fdec = FuncDecl("f", Seq(A, B), C)
        val sig = Signature.empty
            .withSorts(A, B, C)
            .withFunctionDeclaration(fdec)
            .withConstantDeclarations(h.of(A), j.of(B), z.of(C))

        val checker = new TypeChecker(sig)
        val application = App("f", Seq(h, j))
        val result = checker.visit(application)

        result.sanitizedTerm should be (application)
        result.sort should be (C)
        result.containsConnectives should be (false)
        result.containsQuantifiers should be (false)
    }



    test("Closure relation correct"){
        val f = FuncDecl("f", List(A,A), Sort.Bool);
        val sig = Signature.empty.withSort(A).withFunctionDeclaration(f)
            .withConstantDeclaration(x.of(A))
            .withConstantDeclaration(y.of(A))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        val result = checker.visitClosure(closure);

        result.sanitizedTerm should be (closure);
        result.sort should be (BoolSort);
        result.containsConnectives should be (false);
        result.containsQuantifiers should be (false);
    }

    test("Closure function correct"){
        val f = FuncDecl("f", List(A), A);
        val sig = Signature.empty.withSort(A).withFunctionDeclaration(f)
            .withConstantDeclaration(x.of(A))
            .withConstantDeclaration(y.of(A))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        val result = checker.visitClosure(closure);

        result.sanitizedTerm should be (closure);
        result.sort should be (BoolSort);
        result.containsConnectives should be (false);
        result.containsQuantifiers should be (false);
    }
    
    test ("Closure over different sorts") {
        val f = FuncDecl("f", List(A,B), Sort.Bool);
        val sig = Signature.empty.withSort(A)
            .withSort(B)
            .withFunctionDeclaration(f)
            .withConstantDeclaration(x.of(A))
            .withConstantDeclaration(y.of(B))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        
        a [TypeCheckException.WrongSort] should be thrownBy (checker.visitClosure(closure));
    }

    test ("Closure with bad arguments") {
        val f = FuncDecl("f", List(A,A), Sort.Bool);
        val sig = Signature.empty.withSort(A)
            .withSort(B)
            .withFunctionDeclaration(f)
            .withConstantDeclaration(x.of(A))
            .withConstantDeclaration(y.of(B))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        
        a [TypeCheckException.WrongSort] should be thrownBy (checker.visitClosure(closure));
    }

    test ("Closure with fixed arguments") {
        val f = FuncDecl("f", List(A,A,B), Sort.Bool)
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            .withConstantDeclarations(x.of(A), y.of(A), z.of(B))

        val closure = Closure("f", x, y, Seq(z))

        val checker = new TypeChecker(sig)

        val result = checker.visitClosure(closure)
        
        result.sanitizedTerm should be (closure);
        result.sort should be (BoolSort);
        result.containsConnectives should be (false);
        result.containsQuantifiers should be (false);
    }

    test ("Closure with wrong fixed arguments") {
        val f = FuncDecl("f", List(A,A,B), Sort.Bool)
        val sig = Signature.empty
            .withSorts(A, B)
            .withFunctionDeclaration(f)
            // note z is the wrong sort here
            .withConstantDeclarations(x.of(A), y.of(A), z.of(A))

        val closure = Closure("f", x, y, Seq(z));

        val checker = new TypeChecker(sig);
        
        a [TypeCheckException.WrongSort] should be thrownBy (checker.visitClosure(closure));
    }
}