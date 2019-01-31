import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import static fortress.tfol.Term.*;
import static fortress.tfol.Type.*;
import static fortress.tfol.FuncDecl.*;
import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class ModelFinderTest {
    
    static Theory simpleSatTheory;
    static Theory simpleUnsatTheory;
    
    static Var p;
    
    static ModelFinder modelFinder;
    
    @BeforeClass
    public static void setup() {
        simpleSatTheory = new Theory();
        simpleUnsatTheory = new Theory();
        
        p = Term.mkVar("p", Type.Bool);
        
        simpleSatTheory.addConstant(p);
        simpleSatTheory.addAxiom(mkAnd(p, p));
        
        simpleUnsatTheory.addConstant(p);
        simpleUnsatTheory.addAxiom(mkAnd(p, mkNot(p)));
        
        modelFinder = new ModelFinder(
            new UnscopedTransformer(),
            new Z3CommandLine()
        );
    }
    
    @Test
    public void BasicUnscopedZ3CommandLineOutput() throws IOException {
        StringWriter stringWriter = new StringWriter();
        BufferedWriter bufferedWriter = new BufferedWriter(stringWriter);
        Z3CommandLine.writeSmtLib(simpleSatTheory, bufferedWriter);
        bufferedWriter.flush();
        bufferedWriter.close();
        String satTheoryString = stringWriter.toString();
        
        String expectedSatTheoryString = ""
        + "(declare-const p Bool)\n"
        + "(assert (and p p))\n"
        + "(check-sat)";
        
        assertEquals(expectedSatTheoryString, satTheoryString);
        
        stringWriter = new StringWriter();
        bufferedWriter = new BufferedWriter(stringWriter);
        Z3CommandLine.writeSmtLib(simpleUnsatTheory, bufferedWriter);
        bufferedWriter.flush();
        bufferedWriter.close();
        String unsatTheoryString = stringWriter.toString();
        
        String expectedUnsatTheoryString = ""
        + "(declare-const p Bool)\n"
        + "(assert (and p (not p)))\n"
        + "(check-sat)";
        
        assertEquals(expectedUnsatTheoryString, unsatTheoryString);
    }
    
    @Test
    public void BasicUnscopedZ3CommandLine() {
        Errors.failIf(null == modelFinder);
        Errors.failIf(null == simpleSatTheory);
        ModelFinder.Result satTheoryResult = modelFinder.findModel(simpleSatTheory, 1000);
        assertEquals(ModelFinder.Result.SAT, satTheoryResult);
         
        ModelFinder.Result unsatTheoryResult = modelFinder.findModel(simpleUnsatTheory, 1000);
        assertEquals(ModelFinder.Result.UNSAT, unsatTheoryResult);
    }
    
}
