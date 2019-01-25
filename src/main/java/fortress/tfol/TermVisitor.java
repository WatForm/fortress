package fortress.tfol;

public interface TermVisitor<T> {
    default T visit(Term term) {
        return term.accept(this);
    }
    
    T visitTop(Top term);
    T visitBottom(Bottom term);
    T visitVar(Var term);
    T visitNot(Not term);
    T visitAndList(AndList term);
    T visitOrList(OrList term);
    T visitIff(Iff term);
    T visitImplication(Implication term);
    T visitEq(Eq term);
    T visitApp(App term);
    T visitExists(Exists term);
    T visitForall(Forall term);
    T visitDistinct(Distinct term);
}
