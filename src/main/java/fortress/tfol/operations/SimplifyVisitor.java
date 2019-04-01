package fortress.tfol.operations;

import fortress.tfol.*;
import fortress.data.*;
import fortress.util.Errors;

import java.util.Set;

// Based on the implementation in John Harrison's book
// TODO more simplification is possible
public class SimplifyVisitor implements TermVisitor<Term> {
    
    private StepVisitor stepper;
    
    public SimplifyVisitor() {
        this.stepper = new StepVisitor();
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
    public Term visitNot(Not not) {
        return stepper.visit(not.mapBody(this::visit));
    }
    
    @Override
    public Term visitAndList(AndList and) {
        return stepper.visit(and.mapArguments(this::visit));
    }
    
    @Override
    public Term visitOrList(OrList or) {
        return stepper.visit(or.mapArguments(this::visit));
    }
    
    @Override
    public Term visitDistinct(Distinct dist) {
        return stepper.visit(dist.mapArguments(this::visit));
    }
    
    @Override
    public Term visitImplication(Implication imp) {
        return stepper.visit(imp.mapArguments(this::visit));
    }
    
    @Override
    public Term visitIff(Iff iff) {
        return stepper.visit(iff.mapArguments(this::visit));
    }
    
    @Override
    public Term visitEq(Eq eq) {
        // Eq is assumed to be atomic
        return eq;
    }
    
    @Override
    public Term visitApp(App app) {
        // Apps are atomic
        return app;
    }
    
    @Override
    public Term visitExists(Exists exists) {
        return stepper.visit(exists.mapBody(this::visit));
    }
    
    @Override
    public Term visitForall(Forall forall) {
        return stepper.visit(forall.mapBody(this::visit));
    }
    
    private static class StepVisitor implements TermVisitor<Term> {
        
        private NegationStepVisitor negationStepper;
        
        private StepVisitor() {
            this.negationStepper = new NegationStepVisitor();
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
        public Term visitNot(Not not) {
            return negationStepper.visit(not.getBody());
        }
        
        @Override
        public Term visitAndList(AndList and) {
            if(and.getArguments().contains(Term.mkBottom())) {
                return Term.mkBottom();
            }
            
            ImmutableList<Term> arguments = and.getArguments()
                .filter((Term t) -> ! t.equals(Term.mkTop()));
            
            return Term.mkAndF(arguments);
        }
        
        @Override
        public Term visitOrList(OrList or) {
            if(or.getArguments().contains(Term.mkTop())) {
                return Term.mkTop();
            }
            
            ImmutableList<Term> arguments = or.getArguments()
                .filter((Term t) -> ! t.equals(Term.mkBottom()));
            
            return Term.mkOr(arguments);
        }
        
        @Override
        public Term visitDistinct(Distinct dist) {
            return dist;
        }
        
        @Override
        public Term visitImplication(Implication imp) {
            if(imp.getLeft().equals(Term.mkBottom())
                    || imp.getRight().equals(Term.mkTop())) {
                return Term.mkTop();
            }
            if(imp.getLeft().equals(Term.mkTop())) {
                return imp.getRight();
            }
            if(imp.getRight().equals(Term.mkBottom())) {
                return Term.mkNot(imp.getLeft());
            }
            return imp;
        }
        
        @Override
        public Term visitIff(Iff iff) {
            if(iff.getRight().equals(Term.mkTop())) {
                return iff.getLeft();
            }
            if(iff.getLeft().equals(Term.mkTop())) {
                return iff.getRight();
            }
            if(iff.getRight().equals(Term.mkBottom())) {
                return Term.mkNot(iff.getLeft());
            }
            if(iff.getLeft().equals(Term.mkBottom())) {
                return Term.mkNot(iff.getRight());
            }
            return iff;
        }
        
        @Override
        public Term visitEq(Eq eq) {
            // Eq is atomic
            return eq;
        }
        
        @Override
        public Term visitApp(App app) {
            // App is atomic
            return app;
        }
        
        @Override
        public Term visitExists(Exists exists) {
            // Note that we don't need a signature to check here whether the free
            // free variable is really or a constant. We just want to check if
            // the quantified variable x is within the set of free vars.
            // If x is within free vars union constants, then since it is quantified
            // here it must be a free var.
            Set<Var> freeVars = exists.getBody().freeVarConstSymbols();
            ImmutableList<AnnotatedVar> vars = exists.getVars().filter((AnnotatedVar av) -> freeVars.contains(av.getVar()));
            if(vars.size() == 0) {
                return exists.getBody();
            } else {
                return Term.mkExists(vars, exists.getBody());
            }
        }
        
        @Override
        public Term visitForall(Forall forall) {
            // Note that we don't need a signature to check here whether the free
            // free variable is really or a constant. We just want to check if
            // the quantified variable x is within the set of free vars.
            // If x is within free vars union constants, then since it is quantified
            // here it must be a free var.
            Set<Var> freeVars = forall.getBody().freeVarConstSymbols();
            ImmutableList<AnnotatedVar> vars = forall.getVars().filter((AnnotatedVar av) -> freeVars.contains(av.getVar()));
            if(vars.size() == 0) {
                return forall.getBody();
            } else {
                return Term.mkForall(vars, forall.getBody());
            }
        }
    }
    
    private static class NegationStepVisitor implements TermVisitor<Term> {
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
        public Term visitNot(Not not) {
            return not.getBody();
        }
        @Override
        public Term visitAndList(AndList and) {
            return Term.mkNot(and);
        }
        @Override
        public Term visitOrList(OrList or) {
            return Term.mkNot(or);
        }
        @Override
        public Term visitDistinct(Distinct dist) {
            return Term.mkNot(dist);
        }
        @Override
        public Term visitImplication(Implication imp) {
            return Term.mkNot(imp);
        }
        @Override
        public Term visitIff(Iff iff) {
            return Term.mkNot(iff);
        }
        @Override
        public Term visitEq(Eq eq) {
            return Term.mkNot(eq);
        }
        @Override
        public Term visitApp(App app) {
            return Term.mkNot(app);
        }
        @Override
        public Term visitExists(Exists exists) {
            return Term.mkNot(exists);
        }
        @Override
        public Term visitForall(Forall forall) {
            return Term.mkNot(forall);
        }
    }
    
}
