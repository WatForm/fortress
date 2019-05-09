import fortress.tfol.*;

import java.util.List;

public class Theories {
    
    // Transitive relation R
    // Anti symmetric
    // Anti reflexive
    // BiggerFish: For every x, there exists y such that x R y
    // Should be satisfiable only for infinite domains, or empty domains
    // public static Theory lessThanInfinite = makeLessThanInfinite();
    
    
    
    
    
    
    // Group theory axioms
    
    static Sort G = Sort.mkSortConst("G"); // group type
    static Var e = Term.mkVar("e"); // identity element
    static FuncDecl f = FuncDecl.mkFuncDecl("f", G, G, G); // group operation
    
    public static Theory groupTheory = constructGroupTheory();
    public static Theory nonAbelianGroupTheory = constructNonAbelianGroupTheory();
    
    private static Theory constructGroupTheory() {
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var z = Term.mkVar("z");
        
        Term associativeAxiom = Term.mkForall(List.of(x.of(G), y.of(G), z.of(G)),
            Term.mkEq(
                Term.mkApp("f", Term.mkApp("f", x, y), z),
                Term.mkApp("f", x, Term.mkApp("f", y, z))));
        
        Term identityAxiom = Term.mkForall(x.of(G),
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", x, e), x),
                Term.mkEq(Term.mkApp("f", e, x), x)));
        
        Term inverseAxiom = Term.mkForall(x.of(G), Term.mkExists(y.of(G), 
            Term.mkAnd(
                Term.mkEq(Term.mkApp("f", x, y), e),
                Term.mkEq(Term.mkApp("f", y, x), e))));
                
        return Theory.empty()
            .withSort(G)
            .withConstant(e.of(G))
            .withFunctionDeclaration(f)
            .withAxiom(associativeAxiom)
            .withAxiom(identityAxiom)
            .withAxiom(inverseAxiom);
    }
    
    public static Theory constructNonAbelianGroupTheory() {
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Term abelianAssertion = Term.mkForall(List.of(x.of(G), y.of(G)),
            Term.mkEq(
                Term.mkApp("f", x, y),
                Term.mkApp("f", y, x)));
        return groupTheory.withAxiom(Term.mkNot(abelianAssertion));
    }
}
