import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.tfol.Term.*;
import fortress.tfol.Type.*;
import fortress.tfol.FuncDecl.*;
import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;
import java.util.Optional;
import fortress.tfol.operations.*;

import com.microsoft.z3.*;

public class TheoryToZ3JavaTest {
    
    // TODO Check sexprs match what we expect

    
    @Test
    @Ignore("Test not yet implemented")
    public void basicConversion() {
        
        // Var p = Term.mkVar("p");
        // 
        // Theory simpleSatTheory = Theory.empty()
        //     .withConstant(p.of(Type.Bool))
        //     .withAxiom(Term.mkAnd(p, p));
        // 
        // TheoryToZ3Java converter = new TheoryToZ3Java(simpleSatTheory);
        // Solver s = converter.convert();
        // assertEquals("", s.toString());
    }
}
