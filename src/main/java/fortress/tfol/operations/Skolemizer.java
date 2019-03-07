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
public class Skolemizer extends TermVisitorWithContext<Term> {
    private Term toplevelTerm;
    private NameGenerator gen;
    private Set<FuncDecl> skolemFunctions;
    private Set<AnnotatedVar> skolemConstants;
    
    public Skolemizer(Term toplevelTerm, Signature sig, NameGenerator gen) {
        super(sig);
        this.toplevelTerm = toplevelTerm;
        this.gen = gen;
        this.skolemFunctions = new HashSet();
        this.skolemConstants = new HashSet();
    }
    
    public Term convert() {
        return visit(toplevelTerm);
    }
    
    public Set<FuncDecl> getSkolemFunctions() {
        return skolemFunctions;
    }
    
    public Set<AnnotatedVar> getSkolemConstants() {
        return skolemConstants;
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
                String skolemConstantName = gen.freshName("sk");
                
                AnnotatedVar skolemConstant = Term.mkVar(skolemConstantName).of(av.getType());
                skolemConstants.add(skolemConstant);
                
                temporaryBody = temporaryBody.substitute(av.getVar(), skolemConstant.getVar());
            } else {
                // Skolem function
                String skolemFunctionName = gen.freshName("sk");
                
                List<Type> argumentTypes = new ArrayList();
                List<Term> arguments = new ArrayList();
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
                temporaryBody = temporaryBody.substitute(av.getVar(), skolemApplication, gen);
            }
        }
        return visit(temporaryBody);
    }
    
    public Term visitForallInner(Forall forall) {
        return Term.mkForall(forall.getVars(), visit(forall.getBody()));
    }
}
