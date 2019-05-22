package fortress.msfol

import fortress.interpretation.Interpretation
import fortress.util.Errors
import fortress.msfol.operations.TypeCheckResult

import scala.collection.JavaConverters._
import scala.annotation.varargs
import scala.collection.immutable.Seq // Use immutable seq by default

// TODO Theory needs to check for inconsistencies when adding functions as well.
// e.g. If some term already uses "f" as a variable and we add "f : A -> B".

// The constructor is private -- the only way to make theories outside of this class
// is through the empty and withXYZ methods 
case class Theory private (signature: Signature, scopes: Map[Sort, Int], axioms: Set[Term]) {
    
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
      * sort declaration added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withSort(sort: Sort): Theory = Theory(signature.withSort(sort), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * sort declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    def withSorts(sorts: java.lang.Iterable[Sort]) = Theory(signature.withSorts(sorts), scopes, axioms)
    
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
        
    def withFunctionDeclarations(fdecls: Iterable[FuncDecl]): Theory =
        Theory(signature.withFunctionDeclarations(fdecls), scopes, axioms)
    
    /** Returns a theory consisting of the current theory but with the given
      * function declarations added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object.
      */
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Theory = withFunctionDeclarations(fdecls.asJava)
    
    def withScope(t: Sort, size: Int) = {
        // TODO consistency checking
        Theory(signature, scopes + (t -> size), axioms)
    }
    
    def withScopes(scopes: Map[Sort, Int]) = {
        var theory = this
        scopes.foreach { case (sort, size) => theory = theory.withScope(sort, size) }
        theory
    }
    
    def withEnumSort(t: Sort, values: Seq[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), scopes + (t -> values.size), axioms)
    }
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), scopes + (t -> values.size), axioms)
    }

    /** Given an interpretation, return whether it satisfies all axioms of the original theory
      */
    def verifyInterpretation(interpretation: Interpretation): Boolean = {
        // Some Terms are guaranteed to take in only Bools as args (by the typechecker?)
        // eg. and, or. We assume that the input will be only Top/Bottom and convert to a Scala Boolean.
        def forceTermToBool(term: Term): Boolean = term match{
            case Top => true
            case Bottom => false
        }
        def boolToTerm(b: Boolean): Term = if(b) Top else Bottom

        // TODO maybe coalesce into object for all interpretations
        val constInterpretations: Map[AnnotatedVar, Value] = interpretation.constantInterpretations
        /*def getAppInterpretation(fnName: String, args: Either[Term, Boolean]*): Either[Term, Boolean] = {
            val theoryFuncDecl: FuncDecl = signature.functionDeclarations.filter(fd => fd.name == fnName).head
            val fnInterpretation = interpretation.functionInterpretations(theoryFuncDecl)
            val res = fnInterpretation(args)
        }*/

        // TODO update this to work with more than just constants? Maybe
        val varToAnnotated: Map[String, AnnotatedVar] = signature.constants.map(
            annotatedVar => annotatedVar.variable.name -> annotatedVar
        ).toMap

        def evaluate(term: Term): Term = term match{
            // Top/Bottom are "atomic" terms
            // We also treat EnumValues as "atomic" terms (not 100% sure on this)
            case Top | Bottom | EnumValue(_) => term
            case DomainElement(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
            // Is there a better way than asInstanceOf since we already know it's a Var?
            // Translates the variable **BY STRING NAME** to its interpretation (EnumValue or Boolean for now)
            case Var(x) => evaluate(constInterpretations(varToAnnotated(x)))
            // Since we know not/and/or *should* only take in (eventual) Booleans as arguments,
            // can we just use eval().right.get? Does the type checker stop invalid forms?
            case Not(p) => boolToTerm(!forceTermToBool(evaluate(p)))
            case AndList(args) => boolToTerm(args
                .map(arg => forceTermToBool(evaluate(arg)))
                .reduce((a1, a2) => a1 && a2)
            )
            case OrList(args) => boolToTerm(args
                .map(arg => forceTermToBool(evaluate(arg)))
                .reduce((a1, a2) => a1 || a2)
            )
            case Distinct(args) => ???
            case Implication(p, q) => boolToTerm(
                !forceTermToBool(evaluate(p)) || forceTermToBool(evaluate(q))
            )
            case Iff(p, q) => boolToTerm(
                forceTermToBool(evaluate(p)) == forceTermToBool(evaluate(q))
            )
            // This should be either an equality of EnumValues or equality of Top/Bottom
            // Since these are case classes, equality checks should work as expected
            case Eq(l, r) => boolToTerm(evaluate(l) == evaluate(r))
            case App(fname, args) => ???
            case Forall(vars, body) => ???
            case Exists(vars, body) => ???
        }
        for(axiom <- axioms){
            val result = forceTermToBool(evaluate(axiom))
            println(axiom + " evaluated to " + result)
            if(!result){
                return false
            }
        }
        println("All axioms satisfied")
        true
    }
    
    // End of published interface
    
    def sorts: Set[Sort] = signature.sorts
    def functionDeclarations: Set[FuncDecl] = signature.functionDeclarations
    def constants: Set[AnnotatedVar] = signature.constants
    def enumConstants: Map[Sort, Seq[EnumValue]] = signature.enumConstants
    
    def withoutAxioms: Theory = Theory(signature, scopes, Set.empty)
    
    private def sanitizeAxiom(axiom: Term): Term = {
        // Check axiom typechecks as bool
        // Note that a formula cannot typecheck if it has any free variables (that are not constants of the signature)
        val result: TypeCheckResult = axiom.typeCheck(signature)
        Errors.precondition(result.sort == BoolSort)
        result.sanitizedTerm
    }

    override def toString: String = "\n" + signature.toString + " Axioms <<\n" + axioms.mkString("\n") + ">>\n"
    
}

object Theory {
    /**  Returns a theory with an empty signature and no axioms. */
    def empty: Theory = Theory(Signature.empty, Map.empty, Set.empty)
    
    def mkTheoryWithSignature(signature: Signature): Theory = {
      val scopes = (for ((sort, enumValues) <- signature.enumConstants) yield sort -> enumValues.size).toMap
      Theory(signature, scopes, Set.empty)
    }
}
