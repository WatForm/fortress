import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.inputs.*;
import fortress.msfol.*;
import java.util.List;
import java.util.ArrayList;
import java.io.*;


public class TptpParserTest {

    @Test
    public void abelian() throws IOException {
        ClassLoader classLoader = getClass().getClassLoader();
        File file = new File(classLoader.getResource("abelian.p").getFile());
        FileInputStream fileStream = new FileInputStream(file);
        
        Theory resultTheory = new TptpFofParser().parse(fileStream);
        Sort universeSort = Sort.mkSortConst("_UNIV");
        
        Var A = Term.mkVar("A");
        Var B = Term.mkVar("B");
        Var C = Term.mkVar("C");
        Var e = Term.mkVar("e");
        FuncDecl f = FuncDecl.mkFuncDecl("f", universeSort, universeSort, universeSort);
        
        Term associative = Term.mkForall(List.of(A.of(universeSort), B.of(universeSort), C.of(universeSort)),
            Term.mkEq(
                Term.mkApp("f", Term.mkApp("f", A, B), C),
                Term.mkApp("f", A, Term.mkApp("f", B, C))));
        
        Term identity = Term.mkForall(A.of(universeSort),
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", A, e), A),
                Term.mkEq(Term.mkApp("f", e, A), A)));
        
        Term inverse = Term.mkForall(A.of(universeSort), Term.mkExists(B.of(universeSort), 
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", A, B), e),
                Term.mkEq(Term.mkApp("f", B, A), e))));
        
        Term notAbelian = Term.mkNot(Term.mkForall(List.of(A.of(universeSort), B.of(universeSort)),
            Term.mkEq(Term.mkApp("f", A, B), Term.mkApp("f", B, A))));
        
        Theory expectedTheory = Theory.empty()
            .withSort(universeSort)
            .withConstant(e.of(universeSort))
            .withFunctionDeclaration(f)
            .withAxiom(associative)
            .withAxiom(identity)
            .withAxiom(inverse)
            .withAxiom(notAbelian);
        
        assertEquals(expectedTheory, resultTheory);
    }
}
