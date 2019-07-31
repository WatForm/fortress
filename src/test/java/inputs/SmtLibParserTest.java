import static org.junit.Assert.assertEquals;

import fortress.modelfind.ModelFinder;
import fortress.modelfind.ModelFinderResult;
import org.junit.Test;
import org.junit.Ignore;

import fortress.inputs.*;
import fortress.msfol.*;

import java.util.*;
import java.io.IOException;
import java.io.FileInputStream;
import java.io.File;

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
        
        Sort A = Sort.mkSortConst("A");
        Sort B = Sort.mkSortConst("B");
        expectedTheory = expectedTheory.withSort(A);
        expectedTheory = expectedTheory.withSort(B);
        
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        expectedTheory = expectedTheory.withConstant(x.of(A));
        expectedTheory = expectedTheory.withConstant(y.of(B));
        
        FuncDecl p = FuncDecl.mkFuncDecl("p", A, B, Sort.Bool());
        expectedTheory = expectedTheory.withFunctionDeclaration(p);
        
        expectedTheory = expectedTheory.withAxiom(Term.mkApp("p", x, y));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkTop()));
        
        expectedTheory = expectedTheory.withAxiom(Term.mkExists(x.of(A), Term.mkTop()));
        
        Var q = Term.mkVar("q");
        expectedTheory = expectedTheory.withConstant(q.of(Sort.Bool()));
        
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
        
        Sort V = Sort.mkSortConst("V");
        FuncDecl adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool());
        
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
            .withSort(V)
            .withFunctionDeclaration(adj)
            .withAxiom(undirected)
            .withAxiom(loopless)
            .withAxiom(axiom);
        
        assertEquals(expected, resultTheory);
    }

    @Test
    public void integer_parse_1() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("integers.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);

        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);

        Theory expected = Theory.empty()
                .withAxiom(
                        Term.mkEq(
                                Term.mkPlus(
                                        new IntegerLiteral(1),
                                        new IntegerLiteral(1)),
                                new IntegerLiteral(2)))
                .withAxiom(Term.mkAnd(Arrays.asList(
                        Term.mkGE(new IntegerLiteral(5), new IntegerLiteral(5)),
                        Term.mkGE(new IntegerLiteral(5), new IntegerLiteral(1))
                )));

        assertEquals(expected, resultTheory);
    }

    @Test
    public void integer_parse_2() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("integers2.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);

        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);

        ModelFinder mf = ModelFinder.createDefault();
        mf.setTheory(resultTheory);
        ModelFinderResult res = mf.checkSat();

        assert(res == ModelFinderResult.Sat());
    }

    @Test
    public void bv_parse_1() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("bv1.smt").getFile());
        FileInputStream fileStream = new FileInputStream(file);

        SmtLibParser parser = new SmtLibParser();
        Theory resultTheory = parser.parse(fileStream);

        Sort bv5 = new BitVectorSort(5);

        Theory expected = Theory.empty()
            .withSort(bv5)
            .withConstant((new Var("x")).of(bv5))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("f", Arrays.asList(bv5, bv5), bv5))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("g", Collections.singletonList(bv5), bv5))
            .withAxiom(
                Term.mkEq(
                    Term.mkApp(
                        "f",
                        new Var("x"),
                        new Var("x")),
                    Term.mkBvPlus(
                        new Var("x"),
                        new Var("x")
                    )))
            .withAxiom(
                Term.mkEq(
                    Term.mkApp(
                        "g",
                        new Var("x")),
                    Term.mkBvNeg(new Var("x"))))
            .withAxiom(
                Term.mkEq(
                    Term.mkApp("f",
                        Term.mkApp("g",
                            new Var("x")),
                        new Var("x")),
                    new BitVectorLiteral(0, 5)
                ));

        assertEquals(expected, resultTheory);

        ModelFinder mf = ModelFinder.createDefault();
        mf.setTheory(resultTheory);
        ModelFinderResult res = mf.checkSat();

        assert(res == ModelFinderResult.Sat());
    }
}
