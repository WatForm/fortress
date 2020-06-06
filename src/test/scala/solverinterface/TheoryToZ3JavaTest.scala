import org.scalatest._

import fortress.msfol._
import fortress.symmetry._ 

class TheoryToZ3JavaTest extends UnitSuite {
    
    test("conversion") {
        pending
        
        
        // Original Java test that needs correcting:
        // @Test
        // public void conversion() {
        // 
        //     Var p = Term.mkVar("p");
        //     Var x = Term.mkVar("x");
        //     Var y = Term.mkVar("y");
        //     Var z = Term.mkVar("z");
        // 
        //     Theory theory = Theories.groupTheory;
        // 
        //     TheoryToZ3Java converter = new TheoryToZ3Java(theory);
        //     var result = converter.convert();
        //     Context context = result._1();
        //     Solver solver = result._2();
        // 
        //     Set<String> exprs = Arrays.asList(solver.getAssertions()).stream().map(e -> e.toString()).collect(Collectors.toSet());
        //     Set<String> expectedExprs = Set.of(
        //         "(forall ((x G) (y G) (z G)) (= (f (f x y) z) (f x (f y z))))", // associative
        //         "(forall ((x G)) (and (= (f x e) x) (= (f e x) x)))", // identity
        //         "(forall ((x G)) (exists ((y G)) (and (= (f x y) e) (= (f y x) e))))" // inverse
        //     );
        // 
        //     assertEquals(expectedExprs, exprs);
        // }
    }
}
