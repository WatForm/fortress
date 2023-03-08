package fortress.msfol

import fortress.interpretation.Interpretation
import fortress.util.Errors
import fortress.operations.TypeCheckResult

import scala.language.implicitConversions
import scala.jdk.CollectionConverters._
import scala.annotation.varargs
import fortress.operations.InterpretationVerifier
import fortress.operations.TermOps._

// TODO Theory needs to check for inconsistencies when adding functions as well.
// e.g. If some term already uses "f" as a variable and we add "f : A -> B".

// The constructor is private -- the only way to make theories outside of this class
// is through the empty and withXYZ methods 

/** A first-order logic theory, with a signature of symbols and a set of axioms (logical formulas). */
case class Theory private (signature: Signature, axioms: Set[Term]) {
    
    /** Returns a theory consisting of the current theory but with the given
      * axiom added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withAxiom(axiom: Term): Theory = {
        Theory(signature, axioms + axiom)
    }
    
    /** Returns a theory consisting of the current theory but with the given
      * axioms added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withAxioms(newAxioms: java.lang.Iterable[Term]): Theory = {
        var theory: Theory = this
        newAxioms.forEach { axiom =>
            theory = theory.withAxiom(axiom)
        }
        theory
    }
    
    def withAxioms(newAxioms: Iterable[Term]): Theory = {
        Theory(signature, axioms ++ newAxioms)
    }
    
    /** Returns a theory consisting of the current theory but with the given
      * sort declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withSort(sort: Sort): Theory = Theory(signature.withSort(sort), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * sort declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withSorts(sorts: java.lang.Iterable[Sort]) = Theory(signature.withSorts(sorts), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * sort declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withSorts(sorts: Sort*): Theory = withSorts(sorts.asJava)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withConstant(constant: AnnotatedVar): Theory = Theory(signature.withConstant(constant), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withConstants(constants: java.lang.Iterable[AnnotatedVar]): Theory = Theory(signature.withConstants(constants), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * constant declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withConstants(constants: AnnotatedVar*): Theory = withConstants(constants.asJava)
    
    def withConstants(constants: Iterable[AnnotatedVar]): Theory = Theory(signature.withConstants(constants), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withFunctionDeclaration(f: FuncDecl): Theory = Theory(signature.withFunctionDeclaration(f), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Theory = 
        Theory(signature.withFunctionDeclarations(fdecls), axioms)
        
    def withFunctionDeclarations(fdecls: Iterable[FuncDecl]): Theory =
        Theory(signature.withFunctionDeclarations(fdecls), axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Theory = withFunctionDeclarations(fdecls.asJava)

    def withFunctionDefinition(funcDef: FunctionDefinition): Theory = Theory(signature.withFunctionDefinition(funcDef), axioms)

    def withFunctionDefinitions(funcDefs: java.lang.Iterable[FunctionDefinition]): Theory = Theory(signature.withFunctionDefinitions(funcDefs), axioms)

    def withFunctionDefinitions(funcDefs: Iterable[FunctionDefinition]): Theory = Theory(signature.withFunctionDefinitions(funcDefs), axioms)

    def withFunctionDefinitions(funcDefs: FunctionDefinition*): Theory = Theory(signature.withFunctionDefinitions(funcDefs), axioms)

    def withoutFunctionDefinition(funcDef: FunctionDefinition): Theory = Theory(signature.withoutFunctionDefinition(funcDef), axioms)

    def withoutFunctionDefinitions(funcDefs: java.lang.Iterable[FunctionDefinition]): Theory = Theory(signature.withoutFunctionDefinitions(funcDefs), axioms)

    def withoutFunctionDefinitions(funcDefs: Iterable[FunctionDefinition]): Theory = Theory(signature.withoutFunctionDefinitions(funcDefs), axioms)
    
    def withoutFunctionDefinitions(): Theory = Theory(signature.withoutFunctionDefinitions, axioms)
    @varargs
    def withEnumSort(t: Sort, values: EnumValue*): Theory = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), axioms)
    }
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), axioms)
    }
    
    // End of published interface
    
    def sorts: Set[Sort] = signature.sorts
    def sortsJava: java.util.Set[Sort] = signature.sorts.asJava
    def functionDeclarations: Set[FuncDecl] = signature.functionDeclarations

    def functionDefinitions: Set[FunctionDefinition] = signature.functionDefinitions

    def constants: Set[AnnotatedVar] = signature.constants
    def enumConstants: Map[Sort, Seq[EnumValue]] = signature.enumConstants

    override def toString: String = "\n" + signature.toString + "\nAxioms\n" + axioms.mkString("\n") + "\n"
    
}

object Theory {
    /**  Returns a theory with an empty signature and no axioms. */
    def empty: Theory = Theory(Signature.empty, Set.empty)
    
    def mkTheoryWithSignature(signature: Signature): Theory = Theory(signature, Set.empty)
}
