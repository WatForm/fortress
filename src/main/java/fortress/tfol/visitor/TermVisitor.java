package fortress.tfol.visitor;

import fortress.tfol.*;

public interface TermVisitor<T> {
    default public T visit(Term term) {
        return term.accept(this);
    }
    
    public T visitTop(Top term);
    public T visitBottom(Bottom term);
    public T visitVar(Var term);
    public T visitNot(Not term);
    public T visitAndList(AndList term);
    public T visitOrList(OrList term);
    public T visitDistinct(Distinct term);
    public T visitIff(Iff term);
    public T visitImplication(Implication term);
    public T visitEq(Eq term);
    public T visitApp(App term);
    public T visitExists(Exists term);
    public T visitForall(Forall term);
}
