package fortress.msfol.operations;

import fortress.msfol.*;

public interface TermVisitor<T> {
    default public T visit(Term term) {
        return term.accept(this);
    }
    
    public T visitTop();
    public T visitBottom();
    public T visitVar(Var var);
    public T visitEnumValue(EnumValue e);
    public T visitDomainElement(DomainElement d);
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
    public T visitIntegerLiteral(IntegerLiteral literal);
    public T visitBitVectorLiteral(BitVectorLiteral literal);
}
