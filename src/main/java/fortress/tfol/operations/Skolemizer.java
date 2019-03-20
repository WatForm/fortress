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

// Skolemizes a given term
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.
public class Skolemizer {
    private Term toplevelTerm;
    private NameGenerator nameGen;
    private Set<FuncDecl> skolemFunctions;
    private Set<AnnotatedVar> skolemConstants;
    private SkolemVisitor visitor;
    
    /** Creates a Skolemizer primes to Skolemize the given topLevelTerm.
    * When creating new skolem functions or constants, and also when introducing
    * new variables while making substitutions (@see Substituter), the provided
    * name generator will be used.
    * This will mutate the name generator.
    */
    public Skolemizer(Term toplevelTerm, Signature signature, NameGenerator nameGen) {
        this.toplevelTerm = toplevelTerm;
        this.nameGen = nameGen;
        this.skolemFunctions = new HashSet();
        this.skolemConstants = new HashSet();
        this.visitor = new SkolemVisitor(signature);
    }
    
    /**
    * Perform the skolemization and get the resulting term.
    * Don't forget to call getSkolemFunctions() and getSkolemConstants()
    * after this.
    * Convert should only be called once per Skolemizer object.
    */
    public Term convert() {
        return visitor.visit(toplevelTerm);
    }
    
    /**
    * Returns the set of generated skolem functions. Must be called after convert.
    */
    public Set<FuncDecl> getSkolemFunctions() {
        return skolemFunctions;
    }
    
    /**
    * Returns the set of generated skolem functions. Must be called after convert.
    */
    public Set<AnnotatedVar> getSkolemConstants() {
        return skolemConstants;
    }
    
    private class SkolemVisitor extends TermVisitorWithContext<Term> {
        
        public SkolemVisitor(Signature signature) {
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
            return Term.mkNot(visit(not.getBody()));
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
                        Errors.failIf(!typeMaybe.isPresent(), "Type of variable " + v.getName() + " could not be found");
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
        
        public Term visitForallInner(Forall forall) {
            return Term.mkForall(forall.getVars(), visit(forall.getBody()));
        }
    }
}
