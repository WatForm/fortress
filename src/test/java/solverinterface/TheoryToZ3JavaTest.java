import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.msfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;
import java.util.Optional;
import fortress.msfol.operations.*;
import fortress.util.Pair;
import java.util.stream.Collectors;
import java.util.Arrays;

import fortress.outputs.*;

import com.microsoft.z3.*;

public class TheoryToZ3JavaTest {
    
    @Test
    public void conversion() {
        
        Var p = Term.mkVar("p");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var z = Term.mkVar("z");
        
        Theory theory = Theories.groupTheory;
        
        TheoryToZ3Java converter = new TheoryToZ3Java(theory);
        var result = converter.convert();
        Context context = result._1();
        Solver solver = result._2();
        
        Set<String> exprs = Arrays.asList(solver.getAssertions()).stream().map(e -> e.toString()).collect(Collectors.toSet());
        Set<String> expectedExprs = Set.of(
            "(forall ((x G) (y G) (z G)) (= (f (f x y) z) (f x (f y z))))", // associative
            "(forall ((x G)) (and (= (f x e) x) (= (f e x) x)))", // identity
            "(forall ((x G)) (exists ((y G)) (and (= (f x y) e) (= (f y x) e))))" // inverse
        );
        
        assertEquals(expectedExprs, exprs);
    }
}
