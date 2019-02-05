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
import cyclops.data.ImmutableSet;
import cyclops.data.HashSet;

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
    // TODO need to test function declarations, etc are as expected
    public void abelian() throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(abelianInput);
        FOFTPTPLexer lexer = new FOFTPTPLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        TptpToFortress converter = new TptpToFortress();
        converter.visit(tree);
        Theory resultTheory = converter.getTheory();
        
        Theory expectedTheory = new Theory();
        
        Type universeType = converter.getUniverseType();
        expectedTheory.addType(universeType);
        
        Var A = Term.mkVar("A");
        Var B = Term.mkVar("B");
        Var C = Term.mkVar("C");
        Var e = Term.mkVar("e");
        FuncDecl f = FuncDecl.mkFuncDecl("f", universeType, universeType, universeType);
        expectedTheory.addConstant(e.of(universeType));
        expectedTheory.addFunctionDeclaration(f);
        
        Term associative = Term.mkForall(List.of(A.of(universeType), B.of(universeType), C.of(universeType)),
            Term.mkEq(
                Term.mkApp("f", Term.mkApp("f", A, B), C),
                Term.mkApp("f", A, Term.mkApp("f", B, C))));
        
        Term identity = Term.mkForall(A.of(universeType),
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", A, e), A),
                Term.mkEq(Term.mkApp("f", e, A), A)));
        
        Term inverse = Term.mkForall(A.of(universeType), Term.mkExists(B.of(universeType), 
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", A, B), e),
                Term.mkEq(Term.mkApp("f", B, A), e))));
        
        Term notAbelian = Term.mkNot(Term.mkForall(List.of(A.of(universeType), B.of(universeType)),
            Term.mkEq(Term.mkApp("f", A, B), Term.mkApp("f", B, A))));
            
        expectedTheory.addAxiom(associative);
        expectedTheory.addAxiom(identity);
        expectedTheory.addAxiom(inverse);
        expectedTheory.addAxiom(notAbelian);
        
        assertEquals(expectedTheory, resultTheory);
    }
}
