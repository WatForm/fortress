package fortress.tfol;

import fortress.sexpr.*;
import java.util.List;
import java.util.ArrayList;

class SmtExprVisitor implements TermVisitor<SExpr> {
    
    // TODO there is room for duplication removal
    
    @Override
    public SExpr visitTop(Top term) {
        return new StrExpr("true");
    }
    
    @Override
    public SExpr visitBottom(Bottom term) {
        return new StrExpr("false");
    }
    
    @Override
    public SExpr visitVar(Var term) {
        return new StrExpr(term.getName());
    }
    
    @Override
    public SExpr visitNot(Not term) {
        return new ComExpr(
            new StrExpr("not"),
            visit(term.getBody())
        );
    }
    
    @Override
    public SExpr visitAndList(AndList term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(new StrExpr("and"));
        for(Term t : term.getArguments()) {
            expressions.add(visit(t));
        }
        return new ComExpr(expressions);
    }
    
    @Override
    public SExpr visitOrList(OrList term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(new StrExpr("or"));
        for(Term t : term.getArguments()) {
            expressions.add(visit(t));
        }
        return new ComExpr(expressions);
    }
    
    @Override
    public SExpr visitDistinct(Distinct term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(new StrExpr("distinct"));
        for(Var v : term.getVars()) {
            expressions.add(visit(v));
        }
        return new ComExpr(expressions);
    }
    
    @Override
    public SExpr visitIff(Iff term) {
        return new ComExpr(
            new StrExpr("<=>"),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitImplication(Implication term) {
        return new ComExpr(
            new StrExpr("=>"),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitEq(Eq term) {
        return new ComExpr(
            new StrExpr("="),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitApp(App app) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(new StrExpr(app.getFunctionName()));
        for(Term arg : app.getArguments()) {
            expressions.add(visit(arg));
        }
        return new ComExpr(expressions);
    }
    
    @Override
    public SExpr visitExists(Exists term) {
        List<SExpr> variableExpressions = new ArrayList<>();
        for(AnnotatedVar v : term.getVars()) {
            variableExpressions.add(
                new ComExpr(
                    new StrExpr(v.getName()),
                    new StrExpr(v.getType().toString())
                )
            );
        }
        return new ComExpr(
            new StrExpr("exists"),
            new ComExpr(variableExpressions),
            visit(term.getBody())
        );
    }
    
    @Override
    public SExpr visitForall(Forall term) {
        List<SExpr> variableExpressions = new ArrayList<>();
        for(AnnotatedVar v : term.getVars()) {
            variableExpressions.add(
                new ComExpr(
                    new StrExpr(v.getName()),
                    new StrExpr(v.getType().toString())
                )
            );
        }
        return new ComExpr(
            new StrExpr("forall"),
            new ComExpr(variableExpressions),
            visit(term.getBody())
        );
    }
    
}
