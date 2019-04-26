package fortress.tfol.operations;

import fortress.tfol.*;
import fortress.data.NameGenerator;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.lang.IllegalArgumentException;
import fortress.util.Errors;
import java.util.Optional;

// Removes closure given a term, which must be in negation normal form.
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.
public class ClosureEliminator {
    private Term toplevelTerm;
    private NameGenerator nameGen;
    private Set<FuncDecl> closureFunctions;
    private ClosureVisitor visitor;
    
    public ClosureEliminator(Term toplevelTerm, Signature signature, NameGenerator nameGen) {
        this.toplevelTerm = toplevelTerm;
        this.nameGen = nameGen;
        this.closureFunctions = new HashSet<>();
        this.visitor = new ClosureVisitor(signature);
    }
    
    public Term convert() {
        return visitor.visit(toplevelTerm);
    }
    
    /**
    * Returns the set of generated closure functions. Must be called after convert.
    */
    public Set<FuncDecl> getSkolemFunctions() {
        return skolemFunctions;
    }
    
    private class ClosureVisitor extends TermVisitorWithTypeContext<Term> {
        
        public ClosureVisitor(Signature signature) {
            super(signature);
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
        public Term visitVar(Var variable) {
            return variable;
        }
        
        @Override
        public Term visitNot(Not not) {
            return not.mapBody(this::visit);
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
        public Term visitDistinct(Distinct distinct) {
            throw new IllegalArgumentException("Term supposed to be in NNF but found distinct: " + distinct.toString());
        }
        
        @Override
        public Term visitIff(Iff iff) {
            throw new IllegalArgumentException("Term supposed to be in NNF but found iff: " + iff.toString());
        }
        
        @Override
        public Term visitImplication(Implication imp) {
            throw new IllegalArgumentException("Term supposed to be in NNF but found imp: " + imp.toString());
        }
        
        @Override
        public Term visitEq(Eq eq) {
            return eq.mapArguments(this::visit);
        }
        
        public Term visitApp(App app) {
            return app.mapArguments(this::visit);
        }
        
        public Term visitExistsInner(Exists exists) {
            return Term.mkExists(exists.getVars(), visit(exists.getBody()));
        }

        public Term visitForallInner(Forall forall) {
            return Term.mkForall(forall.getVars(), visit(forall.getBody()));
        }
        
        @Override
        public Term visitDomainElement(DomainElement d) {
            return d;
        }
        
        @Override
        public Term visitTC(TC tc) {
            Term temporaryBody = exists.getBody();
            for(AnnotatedVar av: exists.getVars()) {
                Set<Var> freeVars = exists.freeVars(signature);
                if(freeVars.size() == 0) {
                    // Skolem Constant
                    String skolemConstantName = nameGen.freshName("sk");
                    
                    AnnotatedVar skolemConstant = Term.mkVar(skolemConstantName).of(av.getType());
                    skolemConstants.add(skolemConstant);
                    
                    temporaryBody = temporaryBody.substitute(av.getVar(), skolemConstant.getVar());
                    
                    // We also have to update the signature with the new skolem constant
                    // since it might now appear deeper in the new term
                    // Failing to do this was a former bug
                    signature = signature.withConstant(skolemConstant);
                } else {
                    // Skolem function
                    String skolemFunctionName = nameGen.freshName("sk");
                    
                    List<Type> argumentTypes = new ArrayList<>();
                    List<Term> arguments = new ArrayList<>();
                    for(Var v : freeVars) {
                        Optional<Type> typeMaybe = lookupType(v);
                        Errors.assertion(typeMaybe.isPresent(), "Type of variable " + v.getName() + " could not be found");
                        Type type = typeMaybe.get();
                        
                        argumentTypes.add(type);
                        arguments.add(v);
                    }
                    
                    FuncDecl skolemFunction = FuncDecl.mkFuncDecl(skolemFunctionName, argumentTypes, av.getType());
                    skolemFunctions.add(skolemFunction);
                    
                    Term skolemApplication = Term.mkApp(skolemFunctionName, arguments);
                    temporaryBody = temporaryBody.substitute(av.getVar(), skolemApplication, nameGen);
                    
                    signature = signature.withFunctionDeclaration(skolemFunction);
                }
            }
            return visit(temporaryBody);
        }
        
        @Override
        public Term visitIntegerLiteral(IntegerLiteral literal) {
            return fortress.util.Errors.<Term>notImplemented();
        }
        
        @Override
        public Term visitBitVectorLiteral(BitVectorLiteral literal) {
            return fortress.util.Errors.<Term>notImplemented();
        }
    }
}
