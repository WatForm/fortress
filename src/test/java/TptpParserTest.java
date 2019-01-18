import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import fortress.formats.tptp.*;
import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;
import java.io.IOException;
import java.util.Set;
import java.util.HashSet;

public class TptpParserTest {
    
    /*
    Group Theory example
    The universe is described as a group
    The group is conjectured to be abelian
    The following link should tell you for which sizes non-abelian groups exist for
    https://en.wikipedia.org/wiki/List_of_small_groups#List_of_small_non-abelian_groups
    Note that any prime sized group will be abelian, since they are cyclic and cyclic groups are abelian
    */
    
    String abelianInput = ""
    + "fof(associative, axiom, ("
    + "   ! [A, B, C] : (f(f(A, B), C) = f(A, f(B, C)))"
    + "   ))."

    + " fof(identity, axiom, ("
    + "   ! [A] : ((f(A, e) = A) & (f(e, A) = A))"
    + "   ))."

    + " fof(inverse, axiom, ("
    + "   ! [A] : (? [B] : ((f(A, B) = e) & (f(B, A) = e)))"
    + "   ))."

    + " fof(abelian, conjecture, ("
    + "  ! [A, B] : (f(A, B) = f(B, A))"
    + "   )).";

    @Test
    // @Ignore ("Test not implemented; need to double check")
    public void abelian() throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(abelianInput);
        FOFTPTPLexer lexer = new FOFTPTPLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        TptpToFortress converter = new TptpToFortress();
        converter.visit(tree);
        Theory theory = converter.getTheory();
        
        Type universeType = converter.getUniverseType();
        Var A = Term.mkVar("A", universeType);
        Var B = Term.mkVar("B", universeType);
        Var C = Term.mkVar("C", universeType);
        Var e = Term.mkVar("e", universeType);
        FuncDecl f = FuncDecl.mkFuncDecl("f", universeType, universeType, universeType);
        
        List<Var> assocVars = new ArrayList<>();
        assocVars.add(A);
        assocVars.add(B);
        assocVars.add(C);
        Term associative = Term.mkForall(assocVars,
            Term.mkEq(
                Term.mkApp(f, Term.mkApp(f, A, B), C),
                Term.mkApp(f, A, Term.mkApp(f, B, C))));
        Term identity = Term.mkForall(A,
            Term.mkAnd(
                Term.mkEq(Term.mkApp(f, A, e), A),
                Term.mkEq(Term.mkApp(f, e, A), A)));
        Term inverse = Term.mkForall(A, Term.mkExists(B, 
            Term.mkAnd(
                Term.mkEq(Term.mkApp(f, A, B), e),
                Term.mkEq(Term.mkApp(f, B, A), e))));
        List<Var> notAbelianVars = new ArrayList<>();
        notAbelianVars.add(A);
        notAbelianVars.add(B);
        Term notAbelian = Term.mkNot(Term.mkForall(notAbelianVars,
            Term.mkEq(Term.mkApp(f, A, B), Term.mkApp(f, B, A))));
        
        Set<Term> expectedTerms = new HashSet<>();
        expectedTerms.add(associative);
        expectedTerms.add(identity);
        expectedTerms.add(inverse);
        expectedTerms.add(notAbelian);
        assertEquals(expectedTerms, theory.getAxioms());
    }
}
