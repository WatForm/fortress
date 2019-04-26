package fortress.outputs;

import fortress.sexpr.SExpr;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.*;
import fortress.tfol.operations.TermVisitor;

public class SmtExprVisitor implements TermVisitor<SExpr> {
    
    // TODO there is room for duplication removal
    
    @Override
    public SExpr visitTop(Top term) {
        return SExpr.mkAtom("true");
    }
    
    @Override
    public SExpr visitBottom(Bottom term) {
        return SExpr.mkAtom("false");
    }
    
    @Override
    public SExpr visitVar(Var term) {
        return SExpr.mkAtom(term.getName());
    }
    
    @Override
    public SExpr visitNot(Not term) {
        return SExpr.mkList(
            SExpr.mkAtom("not"),
            visit(term.getBody())
        );
    }
    
    @Override
    public SExpr visitAndList(AndList term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(SExpr.mkAtom("and"));
        for(Term t : term.getArguments()) {
            expressions.add(visit(t));
        }
        return SExpr.mkList(expressions);
    }
    
    @Override
    public SExpr visitOrList(OrList term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(SExpr.mkAtom("or"));
        for(Term t : term.getArguments()) {
            expressions.add(visit(t));
        }
        return SExpr.mkList(expressions);
    }
    
    @Override
    public SExpr visitDistinct(Distinct term) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(SExpr.mkAtom("distinct"));
        for(Term t : term.getArguments()) {
            expressions.add(visit(t));
        }
        return SExpr.mkList(expressions);
    }
    
    @Override
    public SExpr visitImplication(Implication term) {
        return SExpr.mkList(
            SExpr.mkAtom("=>"),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitIff(Iff term) {
        return SExpr.mkList(
            SExpr.mkAtom("="),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitEq(Eq term) {
        return SExpr.mkList(
            SExpr.mkAtom("="),
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    @Override
    public SExpr visitApp(App app) {
        List<SExpr> expressions = new ArrayList<>();
        expressions.add(SExpr.mkAtom(app.getFunctionName()));
        for(Term arg : app.getArguments()) {
            expressions.add(visit(arg));
        }
        return SExpr.mkList(expressions);
    }
    
    @Override
    public SExpr visitExists(Exists term) {
        List<SExpr> variableExpressions = new ArrayList<>();
        for(AnnotatedVar v : term.getVars()) {
            variableExpressions.add(
                SExpr.mkList(
                    SExpr.mkAtom(v.getName()),
                    SExpr.mkAtom(v.getType().getName())
                )
            );
        }
        return SExpr.mkList(
            SExpr.mkAtom("exists"),
            SExpr.mkList(variableExpressions),
            visit(term.getBody())
        );
    }
    
    @Override
    public SExpr visitForall(Forall term) {
        List<SExpr> variableExpressions = new ArrayList<>();
        for(AnnotatedVar v : term.getVars()) {
            variableExpressions.add(
                SExpr.mkList(
                    SExpr.mkAtom(v.getName()),
                    SExpr.mkAtom(v.getType().getName())
                )
            );
        }
        return SExpr.mkList(
            SExpr.mkAtom("forall"),
            SExpr.mkList(variableExpressions),
            visit(term.getBody())
        );
    }
    
    @Override
    public SExpr visitDomainElement(DomainElement d) {
        return fortress.util.Errors.<SExpr>notImplemented();
    }
    
    @Override
    public SExpr visitTC(TC tc) {
        throw new IllegalArgumentException("Term must not have TC: " + tc.toString());
    }
    
    @Override
    public SExpr visitIntegerLiteral(IntegerLiteral literal) {
        return fortress.util.Errors.<SExpr>notImplemented();
    }
    
    @Override
    public SExpr visitBitVectorLiteral(BitVectorLiteral literal) {
        return fortress.util.Errors.<SExpr>notImplemented();
    }
    
}
