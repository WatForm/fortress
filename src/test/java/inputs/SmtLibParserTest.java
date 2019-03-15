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
import java.util.Optional;
import java.util.Map;

public class SmtLibParserTest {

    @Test
    public void sample1() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("sample1.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);
        Map<String, String> info = parser.getInfo();
        Optional<String> logic = parser.getLogic();
        
        assertEquals(Optional.of("UF"), logic);
        
        String source = "\nThis is just a test really.\n";
        
        Map<String, String> expectedInfo = Map.of(
            "smt-lib-version", "2.6",
            "status", "sat",
            "category", "toyExample",
            "source", source
        );
        
        assertEquals(expectedInfo, info);
        
        Theory expectedTheory = Theory.empty();
        
        Type A = Type.mkTypeConst("A");
        Type B = Type.mkTypeConst("B");
        expectedTheory = expectedTheory.withType(A);
        expectedTheory = expectedTheory.withType(B);
        
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        expectedTheory = expectedTheory.withConstant(x.of(A));
        expectedTheory = expectedTheory.withConstant(y.of(B));
        
        FuncDecl p = FuncDecl.mkFuncDecl("p", A, B, Type.Bool);
        expectedTheory = expectedTheory.withFunctionDeclaration(p);
        
        expectedTheory = expectedTheory.withAxiom(Term.mkApp("p", x, y));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkTop()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkExists(x.of(A), Term.mkTop()));
        
        Var q = Term.mkVar("q");
        expectedTheory = expectedTheory.withConstant(q.of(Type.Bool));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkOr(q, Term.mkNot(q)));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkAnd(q, q));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkNot(Term.mkBottom()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkDistinct(q, Term.mkBottom()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkEq(q, q));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkImp(Term.mkBottom(), Term.mkTop()));
        
        FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
        FuncDecl g = FuncDecl.mkFuncDecl("g", A, A);
        expectedTheory = expectedTheory.withFunctionDeclaration(f);
        expectedTheory = expectedTheory.withFunctionDeclaration(g);
        
        Var a = Term.mkVar("a");
        Var b = Term.mkVar("b");
        Var c = Term.mkVar("c");
        expectedTheory = expectedTheory.withConstant(a.of(A));
        expectedTheory = expectedTheory.withConstant(b.of(A));
        expectedTheory = expectedTheory.withConstant(c.of(A));
        
        expectedTheory = expectedTheory.withAxiom(
            Term.mkForall(x.of(A),
                Term.mkEq(
                    Term.mkApp("f",
                        Term.mkApp("g", x)),
                    x)));
        
        assertEquals(expectedTheory, resultTheory);
    }   
}
