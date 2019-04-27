package fortress.tfol.operations;

import fortress.tfol.*;
import fortress.data.NameGenerator;
import java.util.List;
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
            if (!signature.hasFunctionWithName(closureName)) {
                List<Type> argTypes = signature.queryUninterpretedFunctionJava(relationName).get().getArgTypes();
                Type type = argTypes.get(0);
                closureFunctions.add(FuncDecl.mkFuncDecl(closureName, type, type, Type.Bool()));
                Var x = Term.mkVar(nameGen.freshName("x")), y = Term.mkVar(nameGen.freshName("y")), z = Term.mkVar(nameGen.freshName("z"));
                AnnotatedVar ax = x.of(type), ay = y.of(type), az = z.of(type);
                Integer scope = scopes.get(type);
                if (scope < 8) {
                    for (scope /= 2; scope > 1; scope /= 2) {
                        String newFunctionName = nameGen.freshName(relationName);
                        closureFunctions.add(FuncDecl.mkFuncDecl(newFunctionName, type, type, Type.Bool()));
                        closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkEq(Term.mkApp(newFunctionName, x, y), Term.mkOr(Term.mkApp(relationName, x, y), Term.mkExists(az, Term.mkAnd(Term.mkApp(relationName, x, z), Term.mkApp(relationName, z, y)))))));
                        relationName = newFunctionName;
                    }
                    closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkEq(Term.mkApp(closureName, x, y), Term.mkOr(Term.mkApp(relationName, x, y), Term.mkExists(az, Term.mkAnd(Term.mkApp(relationName, x, z), Term.mkApp(relationName, z, y)))))));
                } else {
                    String helperName = nameGen.freshName(relationName);
                    String reflexiveClosureName = "*" + relationName;
                    closureFunctions.add(FuncDecl.mkFuncDecl(helperName, type, type, type, Type.Bool()));
                    closureFunctions.add(FuncDecl.mkFuncDecl(reflexiveClosureName, type, type, Type.Bool()));
                    Var u = Term.mkVar(nameGen.freshName("u"));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkNot(Term.mkApp(helperName, x, x, y))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay, az, u.of(type)), Term.mkImp(Term.mkAnd(Term.mkApp(helperName, x, y, u), Term.mkApp(helperName, y, z, u)), Term.mkApp(helperName, x, z, u))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay, az), Term.mkImp(Term.mkAnd(Term.mkApp(helperName, x, y, y), Term.mkApp(helperName, y, z, z), Term.mkNot(Term.mkEq(x, z))), Term.mkApp(helperName, x, z, z))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay, az), Term.mkImp(Term.mkAnd(Term.mkApp(helperName, x, y, z), Term.mkNot(Term.mkEq(y, z))), Term.mkApp(helperName, y, z, z))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkEq(Term.mkApp(reflexiveClosureName, x, y), Term.mkOr(Term.mkApp(helperName, x, y, y), Term.mkEq(x, y)))));
                    Term t = (argTypes.size() == 1) ? Term.mkEq(Term.mkApp(relationName, x), z) : Term.mkApp(relationName, x, z);
                    closureAxioms.add(Term.mkForall(List.of(ax, az), Term.mkImp(Term.mkAnd(t, Term.mkNot(Term.mkEq(x, z))), Term.mkApp(helperName, x, z, z))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkImp(Term.mkApp(helperName, x, y, y), Term.mkExists(az, Term.mkAnd(t, Term.mkApp(helperName, x, z, y))))));
                    closureAxioms.add(Term.mkForall(List.of(ax, ay), Term.mkEq(Term.mkApp(closureName, x, y), Term.mkExists(az, Term.mkAnd(t, Term.mkApp(reflexiveClosureName, z, y))))));
                }
            }
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
