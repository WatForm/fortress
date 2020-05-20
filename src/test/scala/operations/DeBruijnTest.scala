import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import fortress.msfol._
import fortress.operations.TermOps._

class DeBruijnTest extends FunSuite with Matchers{
    
    val A = Sort.mkSortConst("A");
    
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val b = Var("b")
    val c = Var("c")
    
    val _1 = Var("_1")
    val _2 = Var("_2")
    val _3 = Var("_3")
    val _4 = Var("_4")
    val _5 = Var("_5")
    val _6 = Var("_6")
    
    test("basic Forall Exists") {
        val t1 = Forall(x.of(A), App("p", x));
        val t2 = Exists(x.of(A), App("p", x));
        
        val e1 = Forall(_1.of(A), App("p", _1));
        val e2 = Exists(_1.of(A), App("p", _1));
        
        t1.deBruijn should be (e1)
        t2.deBruijn should be (e2)
    }
    
    test("nested Forall Exists") {
        val t = Forall(x.of(A), Exists(y.of(A), And(App("p", x), App("p", y))));
        val e = Forall(_1.of(A), Exists(_2.of(A), And(App("p", _1), App("p", _2))));
        t.deBruijn should be (e)
    }
    
    test("freeVars Left Alone") {
        val t = Forall(x.of(A), Exists(y.of(A), And(App("p", z), App("p", y))));
        val e = Forall(_1.of(A), Exists(_2.of(A), And(App("p", z), App("p", _2))));
        t.deBruijn should be (e)
    }
    
    test("branching") {
        val t = Forall(x.of(A),
            And(
                Exists(y.of(A), And(App("p", x), App("p", y))),
                Exists(z.of(A), And(App("p", x), App("p", z)))
            ));
        val e = Forall(_1.of(A),
            And(
                Exists(_2.of(A), And(App("p", _1), App("p", _2))),
                Exists(_2.of(A), And(App("p", _1), App("p", _2)))
            ));
        t.deBruijn should be (e)
    }
    
    test("shadow variable") {
        val t1 = Forall(x.of(A), Exists(x.of(A), App("p", x)));
        val t2 = Exists(x.of(A), Forall(x.of(A), App("p", x)));
        val e1 = Forall(_1.of(A), Exists(_2.of(A), App("p", _2)));
        val e2 = Exists(_1.of(A), Forall(_2.of(A), App("p", _2)));
        t1.deBruijn should be (e1)
        t2.deBruijn should be (e2)
    }
    
    // TODO: need more tests in other areas that check quantifiers with multiple variables
    
    test("multivar Quantifier") {
        val t1 = Forall(List(x.of(A), y.of(A), z.of(A)), And(
            App("p", x), App("p", z), App("p", y)
        ));
        val t2 = Exists(List(x.of(A), y.of(A), z.of(A)), And(
            App("p", x), App("p", z), App("p", y)
        ));
        val e1 = Forall(List(_1.of(A), _2.of(A), _3.of(A)), And(
            App("p", _1), App("p", _3), App("p", _2)
        ));
        val e2 = Exists(List(_1.of(A), _2.of(A), _3.of(A)), And(
            App("p", _1), App("p", _3), App("p", _2)
        ));
        t1.deBruijn should be (e1)
        t2.deBruijn should be (e2)
    }
    
    test("multivar Quantifier Branch") {
        val t = Forall(List(x.of(A), y.of(A)),
            And(
                Exists(List(x.of(A), y.of(A), z.of(A)),
                    And(App("p", x), App("p", y), App("p", z))),
                Exists(List(y.of(A), z.of(A), x.of(A)),
                    And(App("p", x), App("p", y), App("p", z)))
            ));
        val e = Forall(List(_1.of(A), _2.of(A)),
            And(
                Exists(List(_3.of(A), _4.of(A), _5.of(A)),
                    And(App("p", _3), App("p", _4), App("p", _5))),
                Exists(List(_3.of(A), _4.of(A), _5.of(A)),
                    And(App("p", _5), App("p", _3), App("p", _4)))
            ));
        t.deBruijn should be (e)
    }
}
