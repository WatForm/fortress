import org.scalatest._

import fortress.msfol._
import fortress.operations._
import fortress.data.TypeCheckException

class TypeCheckerTest extends UnitSuite {

    val A = Sort.mkSortConst("A");
    val B = Sort.mkSortConst("B");

    val x = Var("x")
    val y = Var("y")
    val z = Var("z")

    val h = Var("h");
    val j = Var("j");
    val k = Var("k");



    test("Closure relation correct"){
        val f = FuncDecl("f", List(A,A), Sort.Bool);
        val sig = Signature.empty.withSort(A).withFunctionDeclaration(f)
            .withConstant(x.of(A))
            .withConstant(y.of(A))

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
            .withConstant(x.of(A))
            .withConstant(y.of(A))

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
            .withConstant(x.of(A))
            .withConstant(y.of(B))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        
        an [TypeCheckException.WrongSort] should be thrownBy (checker.visitClosure(closure));
    }

    test ("Closure with bad arguments") {
        val f = FuncDecl("f", List(A,A), Sort.Bool);
        val sig = Signature.empty.withSort(A)
            .withSort(B)
            .withFunctionDeclaration(f)
            .withConstant(x.of(A))
            .withConstant(y.of(B))

        val closure = Closure("f", x, y);

        val checker = new TypeChecker(sig);
        
        an [TypeCheckException.WrongSort] should be thrownBy (checker.visitClosure(closure));
    }
}