import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.inputs.*;
import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;
import java.io.IOException;
import java.io.FileInputStream;
import java.io.File;

public class SmtLibParserTest {

    @Test
    public void sample1() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("sample1.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        Theory resultTheory = TheoryParser.parseSmtLib(fileStream);
        
        Theory expectedTheory = Theory.empty();
        
        Type A = Type.mkTypeConst("A");
        Type B = Type.mkTypeConst("B");
        expectedTheory = expectedTheory.withType(A);
        expectedTheory = expectedTheory.withType(B);
        
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        expectedTheory = expectedTheory.withConstant(x.of(A));
        expectedTheory = expectedTheory.withConstant(y.of(B));
        
        FuncDecl decl = FuncDecl.mkFuncDecl("p", A, B, Type.Bool);
        expectedTheory = expectedTheory.withFunctionDeclaration(decl);
        
        expectedTheory = expectedTheory.withAxiom(Term.mkApp("p", x, y));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkTop()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkExists(List.of(x.of(A)), Term.mkTop()));
        
        Var q = Term.mkVar("q");
        expectedTheory = expectedTheory.withConstant(q.of(Type.Bool));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkOr(q, Term.mkNot(q)));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkAnd(q, q));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkNot(Term.mkBottom()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkDistinct(q, Term.mkBottom()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkEq(q, q));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkImp(Term.mkBottom(), Term.mkTop()));
        
        assertEquals(expectedTheory, resultTheory);
    }   
}
