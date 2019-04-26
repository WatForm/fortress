package fortress.tfol.operations;

import fortress.tfol.*;
import fortress.data.NameGenerator;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.lang.IllegalArgumentException;
import fortress.util.Errors;
import java.util.Optional;

// Removes closure given a term, which must be in negation normal form.
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.
public class ClosureEliminator {
    private Term toplevelTerm;
    private Map<Type, Integer> scopes;
    private NameGenerator nameGen;
    private Set<FuncDecl> closureFunctions;
    private Set<Term> closureAxioms;
    private ClosureVisitor visitor;
    
    public ClosureEliminator(Term toplevelTerm, Signature signature, Map<Type, Integer> scopes, NameGenerator nameGen) {
        this.toplevelTerm = toplevelTerm;
        this.scopes = scopes;
        this.nameGen = nameGen;
        this.closureFunctions = new HashSet<>();
        this.closureAxioms = new HashSet<>();
        this.visitor = new ClosureVisitor(signature);
    }
    
    public Term convert() {
        return visitor.visit(toplevelTerm);
    }
    
    /**
    * Returns the set of generated closure functions. Must be called after convert.
    */
    public Set<FuncDecl> getClosureFunctions() {
        return closureFunctions;
    }

    /**
    * Returns the set of axioms defining closure functions. Must be called after convert.
    */
    public Set<Term> getClosureAxioms() {
        return closureAxioms;
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
            String relationName = tc.relationName();
            String closureName = "^" + relationName;
            // if (!signature.hasFunctionWithName(closureName)) {
            //     signature.queryUninterpretedFunctionJava(functionName).ifPresent(f -> {
            //         // TODO: error checking for types of f
            //         Type type = f.getArgTypes().get(0);
            //         FuncDecl closureFunction = FuncDecl.mkFuncDecl(closureName, type, type, Type.Bool());
                    
            //     });
            //     // TODO: throw error if f does not exist
            // }
            return tc.mkApp(closureName).mapArguments(this::visit);
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
