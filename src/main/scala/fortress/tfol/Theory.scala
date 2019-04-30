package fortress.tfol

import fortress.util.Errors
import fortress.tfol.operations.TypeCheckResult
import scala.collection.JavaConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import scala.collection.immutable.Seq // Use immutable seq by default

// TODO Theory needs to check for inconsistencies when adding functions as well.
// e.g. If some term already uses "f" as a variable and we add "f : A -> B".

// The constructor is private -- the only way to make theories outside of this class
// is through the empty and withXYZ methods 
case class Theory private (signature: Signature, scopes: Map[Type, Int], axioms: Set[Term]) {
    
    /** Returns a theory consisting of the current theory but with the given
      * axiom added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object. Throws an exception
      * if the result fails to typecheck with respect to this theory's signature.
      */
    def withAxiom(axiom: Term): Theory = {
        val sanitizedAxiom: Term = sanitizeAxiom(axiom)
        Theory(signature, scopes, axioms + sanitizedAxiom)
    }
    
    /** Returns a theory consisting of the current theory but with the given
      * axioms added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object. Throws an exception
      * if the result fails to typecheck with respect to this theory's signature.
      */
    def withAxioms(newAxioms: java.lang.Iterable[Term]): Theory = {
        var theory: Theory = this
        newAxioms.forEach { axiom =>
            theory = theory.withAxiom(axiom)
        }
        theory
    }
    
    def withAxioms(newAxioms: Iterable[Term]): Theory = {
        val sanitizedAxioms = newAxioms.map(sanitizeAxiom)
        Theory(signature, scopes, axioms ++ sanitizedAxioms)
    }
    
    /** Returns a theory consisting of the current theory but with the given
      * type declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withType(sort: Type): Theory = Theory(signature.withType(sort), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * type declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withTypes(types: java.lang.Iterable[Type]) = Theory(signature.withTypes(types), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * type declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withTypes(types: Type*): Theory = withTypes(types.asJava)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withConstant(constant: AnnotatedVar): Theory = Theory(signature.withConstant(constant), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withConstants(constants: java.lang.Iterable[AnnotatedVar]): Theory = Theory(signature.withConstants(constants), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withConstants(constants: AnnotatedVar*): Theory = withConstants(constants.asJava)
    
    def withConstants(constants: Iterable[AnnotatedVar]): Theory = Theory(signature.withConstants(constants), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withFunctionDeclaration(f: FuncDecl): Theory = Theory(signature.withFunctionDeclaration(f), scopes,  axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Theory = 
        Theory(signature.withFunctionDeclarations(fdecls), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Theory = withFunctionDeclarations(fdecls.asJava)
    
    def withScope(t: Type, size: Int) = {
        // TODO consistency checking
        Theory(signature, scopes + (t -> size), axioms)
    }
    
    def withScopes(scopes: Map[Type, Int]) = {
        var theory = this
        scopes.foreach { case (sort, size) => theory = theory.withScope(sort, size) }
        theory
    }
    
    def withEnumType(t: Type, values: Seq[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumType(t, values), scopes + (t -> values.size), axioms)
    }
    
    def withEnumType(t: Type, values: java.util.List[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumType(t, values), scopes + (t -> values.size), axioms)
    }
    
    // End of published interface
    
    def getAxioms: java.util.Set[Term] = axioms.asJava
    
    def types: Set[Type] = signature.types
    def getTypes: java.util.Set[Type] = signature.getTypes
    
    def getConstants: java.util.Set[AnnotatedVar] = signature.getConstants
    
    def getFunctionDeclarations: java.util.Set[FuncDecl] = signature.getFunctionDeclarations
    
    def getSignature: Signature = signature
    def functionDeclarations: Set[FuncDecl] = signature.functionDeclarations
    def constants: Set[AnnotatedVar] = signature.constants
    
    def enumConstants: Map[Type, Seq[EnumValue]] = signature.enumConstants
    
    def withoutAxioms: Theory = Theory(signature, scopes, Set.empty)
    
    private def sanitizeAxiom(axiom: Term): Term = {
        // Check axiom typechecks as bool
        // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
        val result: TypeCheckResult = axiom.typeCheck(signature)
        Errors.precondition(result.sort == Type.Bool)
        result.term
    }
    
    override def toString(): String = "\n" + signature.toString + " Axioms <<\n" + axioms.mkString("\n") + ">>\n"
    
}

object Theory {
    /**  Returns a theory with an empty signature and no axioms. */
    def empty: Theory = Theory(Signature.empty, Map.empty, Set.empty)
    
    def mkTheoryWithSignature(signature: Signature): Theory = Theory(signature, Map.empty, Set.empty)
}
