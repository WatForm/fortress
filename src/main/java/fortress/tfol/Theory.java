package fortress.tfol;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import java.util.Set;
import fortress.util.Errors;
import java.io.*;
import java.util.Optional;
import java.util.stream.Collectors;
import java.lang.Iterable;
import fortress.tfol.operations.TypeCheckResult;

import fortress.modelfind.*;

public class Theory {
    
    // Published Interface 
    
    /**
    * Returns a theory with an empty signature and no axioms.
    */
    public static Theory empty() {
        return new Theory();
    }
    
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * axiom added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withAxiom(Term formula) {
        Term sanitizedAxiom = sanitizeAxiom(formula);
        return new Theory(signature, axioms.plus(sanitizedAxiom));
    }
    
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * type declaration added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withType(Type type) {
        return new Theory(signature.withType(type), axioms);
    }
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * type declarations added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withTypes(Iterable<Type> types) {
        return new Theory(signature.withTypes(types), axioms);
    }
    
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * constant declaration added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withConstant(AnnotatedVar constant) {
        return new Theory(signature.withConstant(constant), axioms);
    }
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * constant declarations added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withConstants(Iterable<AnnotatedVar> constants) {
        return new Theory(signature.withConstants(constants), axioms);
    }
    
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * function declaration added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withFunctionDeclaration(FuncDecl f) {
        return new Theory(signature.withFunctionDeclaration(f), axioms);
    }
    /**
    * @Publish
    * Returns a theory consisting of the current theory but with the given
    * function declarations added. Note that this does not modify the current Theory object,
    * but rather just returns a new Theory object.
    */
    public Theory withFunctionDeclarations(Iterable<FuncDecl> fdecls) {
        return new Theory(signature.withFunctionDeclarations(fdecls), axioms);
    }
    
    // End of published interface
    
    private final Signature signature;
    private final PersistentSet<Term> axioms;
    
    private Theory() {
        this.signature = Signature.empty();
        this.axioms = PersistentHashSet.empty();
    }
    
    private Theory(Signature signature, PersistentSet<Term> axioms) {
        this.signature = signature;
        this.axioms = axioms;
    }
    
    static public Theory mkTheoryWithSignature(Signature signature) {
        return new Theory(signature, PersistentHashSet.empty());
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
    
    private Term sanitizeAxiom(Term formula) {
        // Check axiom typechecks as bool
        // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
        TypeCheckResult result = formula.typeCheck(signature);
        Errors.failIf(! result.type.equals(Type.Bool));
        return result.term;
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
