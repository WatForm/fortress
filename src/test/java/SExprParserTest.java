import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import fortress.formats.*;
import static fortress.sexpr.SExpr.*;
import fortress.sexpr.SExpr;
import java.util.List;
import java.util.ArrayList;
import java.io.IOException;

public class SExprParserTest {
    
    /*
    Group Theory example
    The universe is described as a group
    The group is conjectured to be abelian
    The following link should tell you for which sizes non-abelian groups exist for
    https://en.wikipedia.org/wiki/List_of_small_groups#List_of_small_non-abelian_groups
    Note that any prime sized group will be abelian, since they are cyclic and cyclic groups are abelian
    */
    
    String basicInput = ""
    + "e1"
    + "(e2)"
    + "(e3 e4)"
    + "(e5 (e6) e7)"
    + "((e8 e9) ())";

    @Test
    // TODO need to test function declarations, etc are as expected
    public void basic() throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(basicInput);
        SimpleSExprLexer lexer = new SimpleSExprLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SimpleSExprParser parser = new SimpleSExprParser(tokens);
        ParseTree tree = parser.s_exprs();
        SExprGenerator converter = new SExprGenerator();
        List<SExpr> exprs = (List<SExpr>) converter.visit(tree);
        
        List<SExpr> expected = new ArrayList();
        expected.add(mkAtom("e1"));
        expected.add(mkList(mkAtom("e2")));
        expected.add(mkList(mkAtom("e3"), mkAtom("e4")));
        expected.add(mkList(mkAtom("e5"), mkList(mkAtom("e6")), mkAtom("e7")));
        expected.add(mkList(mkList(List.of(mkAtom("e8"), mkAtom("e9"))), mkList(new ArrayList())));
        
        assertEquals(expected, exprs);
    }
}
