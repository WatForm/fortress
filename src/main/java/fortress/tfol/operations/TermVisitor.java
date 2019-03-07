package fortress.tfol.operations;

import fortress.tfol.*;

public interface TermVisitor<T> {
    default public T visit(Term term) {
        return term.accept(this);
    }
    
    public T visitTop(Top top);
    public T visitBottom(Bottom bottom);
    public T visitVar(Var var);
    public T visitNot(Not not);
    public T visitAndList(AndList and);
    public T visitOrList(OrList or);
    public T visitDistinct(Distinct dist);
    public T visitImplication(Implication imp);
    public T visitIff(Iff iff);
    public T visitEq(Eq eq);
    public T visitApp(App app);
    public T visitExists(Exists exists);
    public T visitForall(Forall forall);
}
