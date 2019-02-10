package fortress.sexpr;

public interface SExprVisitor<T> {
    default public T visit(SExpr expr) {
        return expr.accept(this);
    }
    
    public T visitStrExpr(StrExpr expr);
    public T visitComExpr(ComExpr expr);
}
