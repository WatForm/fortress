package fortress.formats;

import java.util.List;
import java.util.ArrayList;
import fortress.sexpr.SExpr;

public class SExprGenerator extends SimpleSExprBaseVisitor {
    
    @Override
    public List<SExpr> visitS_exprs(SimpleSExprParser.S_exprsContext ctx) {
        List<SExpr> exprs = new ArrayList();
        for(SimpleSExprParser.S_exprContext exprCtx : ctx.s_expr()) {
            exprs.add((SExpr) visit(exprCtx));
        }
        return exprs;
    }
    
    @Override
    public SExpr visitAtom(SimpleSExprParser.AtomContext ctx) {
        return SExpr.mkAtom(ctx.ID().getText());
    }
    
    @Override
    public SExpr visitList(SimpleSExprParser.ListContext ctx) {
        List<SExpr> exprs = new ArrayList();
        for(SimpleSExprParser.S_exprContext exprCtx : ctx.s_expr()) {
            exprs.add((SExpr) visit(exprCtx));
        }
        return SExpr.mkList(exprs);
    }
}
