package fortress.tfol;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import java.util.Set;
import fortress.util.Errors;
import java.io.*;
import java.util.Optional;
import java.util.stream.Collectors;
import java.lang.Iterable;

import fortress.modelfind.*;

public class Theory {
    private Signature signature;
    private PersistentSet<Term> axioms;

    private Theory() {
        this.signature = signature.empty();
        this.axioms = PersistentHashSet.empty();
    }
    
    private Theory(Signature signature, PersistentSet<Term> axioms) {
        this.signature = signature;
        this.axioms = axioms;
    }
    
    static public Theory mkTheory(Signature signature) {
        return new Theory(signature, PersistentHashSet.empty());
    }
    
    public static Theory empty() {
        return new Theory();
    }
    
    // Returns a new theory object without modifying the previous
    public Theory withAxiom(Term formula) {
        checkAxiom(formula);
        return new Theory(signature, axioms.plus(formula));
    }
    
    // Returns a new theory object without modifying the previous
    public Theory withType(Type type) {
        return new Theory(signature.withType(type), axioms);
    }
    
    // Returns a new theory object without modifying the previous
    public Theory withConstant(AnnotatedVar constant) {
        return new Theory(signature.withConstant(constant), axioms);
    }
    public Theory withConstants(Iterable<AnnotatedVar> constants) {
        return new Theory(signature.withConstants(constants), axioms);
    }
    
    // Returns a new theory object without modifying the previous
    public Theory withFunctionDeclaration(FuncDecl f) {
        return new Theory(signature.withFunctionDeclaration(f), axioms);
    }
    public Theory withFunctionDeclarations(Iterable<FuncDecl> fdecls) {
        return new Theory(signature.withFunctionDeclarations(fdecls), axioms);
    }
    
    public Set<Term> getAxioms() {
        return axioms;
    }
    
    public Set<Type> getTypes() {
        return signature.getTypes();
    }
    
    public Set<AnnotatedVar> getConstants() {
        return signature.getConstants();
    }
    
    public Set<FuncDecl> getFunctionDeclarations() {
        return signature.getFunctionDeclarations();
    }
    
    public Signature getSignature() {
        return signature;
    }
    
    private void checkAxiom(Term formula) {
        // Check axiom typechecks as bool
        // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
        formula.typecheckEither(signature).matchDo(
            (String err) -> Errors.failIf(true, err),
            (Type t) -> Errors.failIf(!t.equals(Type.Bool), "Axiom " + formula.toString() + " has type " + t.getName())
        );
    }
    
    @Override
    public boolean equals(Object other) {
        if(this == other) {
            return true;
        }
        if(null == other) {
            return false;
        }
        if(this.getClass() != other.getClass()) {
            return false;
        }
        Theory o = (Theory) other;
        return this.signature.equals(o.signature)
            && this.axioms.equals(o.axioms);
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + signature.hashCode();
        result = result * prime + axioms.hashCode();
        return result;
    }
    
    //Testing only
    @Override
    public String toString() {
        try {
            StringWriter stringWriter = new StringWriter();
            BufferedWriter bufferedWriter = new BufferedWriter(stringWriter);
            Z3CommandLine.writeSmtLib(this, bufferedWriter);
            bufferedWriter.flush();
            bufferedWriter.close();
            return stringWriter.toString();
        } catch(IOException e) {
            return "ERROR-STRING";
        }
    }
    
}
