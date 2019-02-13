import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import fortress.formats.*;
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
        ANTLRInputStream input = new ANTLRInputStream(fileStream);
        SmtLibSubsetLexer lexer = new SmtLibSubsetLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SmtLibSubsetParser parser = new SmtLibSubsetParser(tokens);
        ParseTree tree = parser.commands();
        SmtLibToTheory converter = new SmtLibToTheory();
        converter.visit(tree);
        Theory resultTheory = converter.getTheory();
        
        Theory expectedTheory = new Theory();
        
        Type A = Type.mkTypeConst("A");
        Type B = Type.mkTypeConst("B");
        expectedTheory.addType(A);
        expectedTheory.addType(B);
        
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        expectedTheory.addConstant(x.of(A));
        expectedTheory.addConstant(y.of(B));
        
        FuncDecl decl = FuncDecl.mkFuncDecl("p", A, B, Type.Bool);
        expectedTheory.addFunctionDeclaration(decl);
        
        expectedTheory.addAxiom(Term.mkApp("p", x, y));
        
        expectedTheory.addAxiom(Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkTop()));
        
        expectedTheory.addAxiom(Term.mkExists(List.of(x.of(A)), Term.mkTop()));
        
        Var q = Term.mkVar("q");
        expectedTheory.addConstant(q.of(Type.Bool));
        
        expectedTheory.addAxiom(Term.mkOr(q, Term.mkNot(q)));
        
        expectedTheory.addAxiom(Term.mkAnd(q, q));
        
        expectedTheory.addAxiom(Term.mkNot(Term.mkBottom()));
        
        expectedTheory.addAxiom(Term.mkDistinct(q, Term.mkBottom()));
        
        expectedTheory.addAxiom(Term.mkEq(q, q));
        
        expectedTheory.addAxiom(Term.mkImp(Term.mkBottom(), Term.mkTop()));
        
        assertEquals(expectedTheory, resultTheory);
    }   
}
