import fortress.tfol.*;

import java.util.List;

public class Theories {
    
    // Transitive relation R
    // Anti symmetric
    // Anti reflexive
    // BiggerFish: For every x, there exists y such that x R y
    // Should be satisfiable only for infinite domains, or empty domains
    // public static Theory lessThanInfinite = makeLessThanInfinite();
    
    static Type groupType = Type.mkTypeConst("G");
    static Var identityElem = Term.mkVar("e", groupType);
    static FuncDecl groupOp = FuncDecl.mkFuncDecl("f", groupType, groupType, groupType);
    
    public static Theory makeGroupTheory() {
        Theory groupTheory = new Theory();
        
        groupTheory.addType(groupType);
        groupTheory.addConstant(identityElem);
        groupTheory.addFunctionSymbol(groupOp);
        
        Var x = Term.mkVar("x", groupType);
        Var y = Term.mkVar("y", groupType);
        Var z = Term.mkVar("z", groupType);
        
        Term associativeAxiom = Term.mkForall(List.of(x, y, z),
            Term.mkEq(
                Term.mkApp(groupOp, Term.mkApp(groupOp, x, y), z),
                Term.mkApp(groupOp, x, Term.mkApp(groupOp, y, z))));
        Term identityAxiom = Term.mkForall(x,
            Term.mkAnd(
                Term.mkEq(Term.mkApp(groupOp, x, identityElem), x),
                Term.mkEq(Term.mkApp(groupOp, identityElem, x), x)));
        Term inverseAxiom = Term.mkForall(x, Term.mkExists(y, 
            Term.mkAnd(
                Term.mkEq(Term.mkApp(groupOp, x, y), identityElem),
                Term.mkEq(Term.mkApp(groupOp, y, x), identityElem))));
                
        groupTheory.addAxiom(associativeAxiom);
        groupTheory.addAxiom(identityAxiom);
        groupTheory.addAxiom(inverseAxiom);
        
        return groupTheory;
    }
    
    public static Theory makeNonAbelianGroupTheory() {
        Theory theory = makeGroupTheory();
        
        Var x = Term.mkVar("x", groupType);
        Var y = Term.mkVar("y", groupType);
        Term abelianAssertion = Term.mkForall(List.of(x, y),
            Term.mkEq(
                Term.mkApp(groupOp, x, y),
                Term.mkApp(groupOp, y, x)));
        theory.addAxiom(Term.mkNot(abelianAssertion));
        return theory;
    }
}
