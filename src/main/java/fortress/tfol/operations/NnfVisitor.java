package fortress.tfol.operations;

import fortress.tfol.*;

import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Optional;
import fortress.util.Errors;
import fortress.data.Either;

// Given a signature and a well-typed formula, compute the negation normal form of the
// formula

// TODO check out the linear time NNF from Harrison's Exercise 2.7
public class NnfVisitor implements TermVisitor<Term> {
    
    private Signature signature;
    private OnceNegatedVisitor onceNegated;
    
    public NnfVisitor(Signature sig) {
        this.signature = sig;
        this.onceNegated = new OnceNegatedVisitor(this);
    }
    
    @Override
    public Term visitTop(Top term) {
        return term;
    }
    
    @Override
    public Term visitBottom(Bottom term) {
        return term;
    }
    
    @Override
    public Term visitVar(Var term) {
        return term;
    }
    
    @Override
    public Term visitAndList(AndList term) {
        List<Term> args = new ArrayList();
        for(Term arg : term.getArguments()) {
            args.add(visit(arg));
        }
        return Term.mkAnd(args);
    }
    
    @Override
    public Term visitOrList(OrList term) {
        List<Term> args = new ArrayList();
        for(Term arg : term.getArguments()) {
            args.add(visit(arg));
        }
        return Term.mkOr(args);
    }
    
    @Override
    public Term visitDistinct(Distinct term) {
        List<Term> args = new ArrayList();
        for(Term arg : term.getArguments()) {
            args.add(visit(arg));
        }
        return visit(term.asPairwiseNotEquals());
    }
    
    @Override
    public Term visitImplication(Implication term) {
        Term l = visit(Term.mkNot(term.getLeft()));
        Term r = visit(term.getRight());
        return Term.mkOr(l, r);
    }
    
    @Override
    public Term visitApp(App term) {
        //NOTE: We assume applications and arguments to applications are atomic
        return term;
    }
    
    @Override
    public Term visitExists(Exists term) {
        return Term.mkExists(term.getVars(), visit(term.getBody()));
    }
    
    @Override
    public Term visitForall(Forall term) {
        return Term.mkForall(term.getVars(), visit(term.getBody()));
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
    public Term visitEq(Eq term) {
        return term;
    }
    
    @Override
    public Term visitNot(Not term) {
        return onceNegated.visit(term.getBody());
    }
    
    // Recur on a term of the form (Not (term))
    // The body of the negation is passed in as the argument, but the
    // return value should act as if there is a negation on it
    class OnceNegatedVisitor implements TermVisitor<Term> {
        private NnfVisitor nnf;
        
        private OnceNegatedVisitor(NnfVisitor nnf) {
            this.nnf = nnf;
        }
        
        @Override
        public Term visitTop(Top term) {
            return Term.mkBottom();
        }
        
        @Override
        public Term visitBottom(Bottom term) {
            return Term.mkTop();
        }
        
        @Override
        public Term visitVar(Var term) {
            return Term.mkNot(term);
        }
        
        @Override
        public Term visitAndList(AndList term) {
            List<Term> args = new ArrayList();
            for(Term arg: term.getArguments()) {
                args.add(nnf.visit(Term.mkNot(arg)));
            }
            return Term.mkOr(args);
        }
        
        @Override
        public Term visitOrList(OrList term) {
            List<Term> args = new ArrayList();
            for(Term arg: term.getArguments()) {
                args.add(nnf.visit(Term.mkNot(arg)));
            }
            return Term.mkAnd(args);
        }
        
        @Override
        public Term visitDistinct(Distinct term) {
            return visit(term.asPairwiseNotEquals());
        }
        
        @Override
        public Term visitImplication(Implication term) {
            return Term.mkAnd(
                nnf.visit(term.getLeft()),
                nnf.visit(Term.mkNot(term.getRight()))
            );
        }
        
        @Override
        public Term visitApp(App term) {
            return Term.mkNot(term);
        }
        
        @Override
        public Term visitExists(Exists term) {
            return Term.mkForall(term.getVars(), nnf.visit(Term.mkNot(term.getBody())));
        }
        
        @Override
        public Term visitForall(Forall term) {
            return Term.mkExists(term.getVars(), nnf.visit(Term.mkNot(term.getBody())));
        }
        
        @Override
        public Term visitIff(Iff term) {
            Term left = term.getLeft();
            Term right = term.getRight();
            return Term.mkOr(
                Term.mkAnd(nnf.visit(left), nnf.visit(Term.mkNot(right))),
                Term.mkAnd(nnf.visit(Term.mkNot(left)), nnf.visit(right))
            );
        }
        
        @Override
        public Term visitEq(Eq term) {
            return Term.mkNot(term);
        }
        
        @Override
        public Term visitNot(Not term) {
            return nnf.visit(term.getBody());
        }
    }
}
