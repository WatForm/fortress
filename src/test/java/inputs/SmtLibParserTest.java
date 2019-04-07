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
    
    @Test(expected = fortress.inputs.ParserException.class)
    public void parserThrowsOnError() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("badParse.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);
    }
    
    @Test(expected = fortress.inputs.LexerException.class)
    public void lexerThrowsOnError() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("badLexical.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);
    }

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
        
        FuncDecl p = FuncDecl.mkFuncDecl("p", A, B, Type.Bool());
        expectedTheory = expectedTheory.withFunctionDeclaration(p);
        
        expectedTheory = expectedTheory.withAxiom(Term.mkApp("p", x, y));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkTop()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkExists(x.of(A), Term.mkTop()));
        
        Var q = Term.mkVar("q");
        expectedTheory = expectedTheory.withConstant(q.of(Type.Bool()));
        
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
    
    @Test
    public void ramsey_coclique_k3_badformulation() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("length-two-paths.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);
        
        Type V = Type.mkTypeConst("V");
        FuncDecl adj = FuncDecl.mkFuncDecl("adj", V, V, Type.Bool());
        
        Var u = Term.mkVar("u");
        Var v = Term.mkVar("v");
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var x3 = Term.mkVar("x3");
        
        Term undirected = Term.mkForall(List.of(u.of(V), v.of(V)), Term.mkEq(Term.mkApp("adj", u, v), Term.mkApp("adj", v, u)));
        Term loopless = Term.mkForall(u.of(V), Term.mkNot(Term.mkApp("adj", u, u)));
        
        Term axiom = Term.mkNot(Term.mkExists(List.of(x1.of(V), x2.of(V), x3.of(V)),
            Term.mkAnd(
                Term.mkDistinct(x1, x2, x3),
                Term.mkEq(
                    Term.mkApp("adj", x1, x2),
                    Term.mkApp("adj", x2, x3)))));
        
        Theory expected = Theory.empty()
            .withType(V)
            .withFunctionDeclaration(adj)
            .withAxiom(undirected)
            .withAxiom(loopless)
            .withAxiom(axiom);
        
        assertEquals(expected, resultTheory);
    }
}
