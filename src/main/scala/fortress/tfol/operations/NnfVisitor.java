package fortress.tfol.operations;

import fortress.tfol.*;

import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Optional;
import fortress.util.Errors;
import fortress.data.ImmutableList;

// Given a signature and a well-typed, santized formula, compute the negation normal form of the
// formula

// TODO check out the linear time NNF from Harrison's Exercise 2.7
public class NnfVisitor implements TermVisitor<Term> {
    
    private OnceNegatedVisitor onceNegated;
    
    public NnfVisitor() {
        this.onceNegated = new OnceNegatedVisitor(this);
    }
    
    @Override
    public Term visitTop(Top top) {
        return top;
    }
    
    @Override
    public Term visitBottom(Bottom bottom) {
        return bottom;
    }
    
    @Override
    public Term visitVar(Var var) {
        return var;
    }
    
    @Override
    public Term visitAndList(AndList and) {
        return and.mapArguments(this::visit);
    }
    
    @Override
    public Term visitOrList(OrList or) {
        return or.mapArguments(this::visit);
    }
    
    @Override
    public Term visitDistinct(Distinct dist) {
        return visit(dist.asPairwiseNotEquals());
    }
    
    @Override
    public Term visitImplication(Implication imp) {
        Term l = visit(Term.mkNot(imp.getLeft()));
        Term r = visit(imp.getRight());
        return Term.mkOr(l, r);
    }
    
    @Override
    public Term visitApp(App app) {
        //NOTE: We assume applications and arguments to applications are atomic
        return app;
    }
    
    @Override
    public Term visitExists(Exists exists) {
        return Term.mkExists(exists.getVars(), visit(exists.getBody()));
    }
    
    @Override
    public Term visitForall(Forall forall) {
        return Term.mkForall(forall.getVars(), visit(forall.getBody()));
    }
    
    @Override
    public Term visitIff(Iff iff) {
        Term left = iff.getLeft();
        Term right = iff.getRight();
        return Term.mkOr(
            Term.mkAnd(visit(left), visit(right)),
            Term.mkAnd(visit(Term.mkNot(left)), visit(Term.mkNot(right)))
        );
    }
    
    @Override
    public Term visitEq(Eq eq) {
        // We assume = is between non-Booleans and so is atomic
        return eq;
    }
    
    @Override
    public Term visitNot(Not not) {
        return onceNegated.visit(not.getBody());
    }
    
    // Recur on a term of the form (Not (term))
    // The body of the negation is passed in as the argument, but the
    // return value should act as if there is a negation on it
    private static class OnceNegatedVisitor implements TermVisitor<Term> {
        private NnfVisitor nnf;
        
        private OnceNegatedVisitor(NnfVisitor nnf) {
            this.nnf = nnf;
        }
        
        @Override
        public Term visitTop(Top top) {
            return Term.mkBottom();
        }
        
        @Override
        public Term visitBottom(Bottom bottom) {
            return Term.mkTop();
        }
        
        @Override
        public Term visitVar(Var var) {
            return Term.mkNot(var);
        }
        
        @Override
        public Term visitAndList(AndList and) {
            ImmutableList<Term> args = and.getArguments().map(
                (Term t) -> nnf.visit(Term.mkNot(t))
            );
            return Term.mkOrF(args);
        }
        
        @Override
        public Term visitOrList(OrList or) {
            ImmutableList<Term> args = or.getArguments().map(
                (Term t) -> nnf.visit(Term.mkNot(t))
            );
            return Term.mkAnd(args);
        }
        
        @Override
        public Term visitDistinct(Distinct dist) {
            return visit(dist.asPairwiseNotEquals());
        }
        
        @Override
        public Term visitImplication(Implication imp) {
            return Term.mkAnd(
                nnf.visit(imp.getLeft()),
                nnf.visit(Term.mkNot(imp.getRight()))
            );
        }
        
        @Override
        public Term visitApp(App app) {
            return Term.mkNot(app);
        }
        
        @Override
        public Term visitExists(Exists exists) {
            return Term.mkForall(exists.getVars(), nnf.visit(Term.mkNot(exists.getBody())));
        }
        
        @Override
        public Term visitForall(Forall forall) {
            return Term.mkExists(forall.getVars(), nnf.visit(Term.mkNot(forall.getBody())));
        }
        
        @Override
        public Term visitIff(Iff iff) {
            Term left = iff.getLeft();
            Term right = iff.getRight();
            return Term.mkOr(
                Term.mkAnd(nnf.visit(left), nnf.visit(Term.mkNot(right))),
                Term.mkAnd(nnf.visit(Term.mkNot(left)), nnf.visit(right))
            );
        }
        
        @Override
        public Term visitEq(Eq eq) {
            // We assume = is between non-Booleans and so is atomic
            return Term.mkNot(eq);
        }
        
        @Override
        public Term visitNot(Not not) {
            return nnf.visit(not.getBody());
        }
    }
}
