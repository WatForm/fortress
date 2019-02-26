import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import static fortress.tfol.Term.*;
import static fortress.tfol.Type.*;
import static fortress.tfol.FuncDecl.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;

public class TheoryWithTest {
    @Test
    // withType should create new theory with type added
    public void withTypeShouldAdd() {
        Type A = Type.mkTypeConst("A");
        Type B = Type.mkTypeConst("B");
        
        Theory theory1 = new Theory();
        assertEquals(Set.of(Type.Bool), theory1.getTypes());
        Theory theory2 = theory1.withType(A);
        assertEquals(Set.of(Type.Bool, A), theory2.getTypes());
        Theory theory3 = theory2.withType(B);
        assertEquals(Set.of(Type.Bool, A, B), theory3.getTypes());
    }
    
    @Test
    // withFunctionDeclaration should create new theory with function declaration added
    public void withFunctionDeclarationShouldAdd() {
        Type A = Type.mkTypeConst("A");
        FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
        FuncDecl p = FuncDecl.mkFuncDecl("p", A, A, Type.Bool);
        
        Theory theory1 = new Theory().withType(A);
        assertEquals(Set.of(), theory1.getFunctionDeclarations());
        Theory theory2 = theory1.withFunctionDeclaration(f);
        assertEquals(Set.of(f), theory2.getFunctionDeclarations());
        Theory theory3 = theory2.withFunctionDeclaration(p);
        assertEquals(Set.of(f, p), theory3.getFunctionDeclarations());
    }
    
    @Test
    // withConstant should create new theory with constant added
    public void withConstantShouldAdd() {
        Type A = Type.mkTypeConst("A");
        AnnotatedVar p = Term.mkVar("p").of(Type.Bool);
        AnnotatedVar c = Term.mkVar("c").of(A);
        
        Theory theory1 = new Theory().withType(A);
        assertEquals(Set.of(), theory1.getConstants());
        Theory theory2 = theory1.withConstant(p);
        assertEquals(Set.of(p), theory2.getConstants());
        Theory theory3 = theory2.withConstant(c);
        assertEquals(Set.of(p, c), theory3.getConstants());
    }
    
    @Test
    // withAxiom should create new theory with axiom added
    public void withAxiomShouldAdd() {
        Term axiom1 = Term.mkNot(Term.mkTop());
        Term axiom2 = Term.mkAnd(axiom1, axiom1);
        
        Theory theory1 = new Theory();
        assertEquals(Set.of(), theory1.getAxioms());
        Theory theory2 = theory1.withAxiom(axiom1);
        assertEquals(Set.of(axiom1), theory2.getAxioms());
        Theory theory3 = theory2.withAxiom(axiom2);
        assertEquals(Set.of(axiom1, axiom2), theory3.getAxioms());
    }
    
}
