package fortress.msfol

import fortress.interpretation.Interpretation
import fortress.util.Errors
import fortress.msfol.operations.TypeCheckResult

import scala.collection.JavaConverters._
import scala.annotation.varargs
import scala.collection.immutable.Seq
import scala.collection.mutable.ListBuffer // Use immutable seq by default

// TODO Theory needs to check for inconsistencies when adding functions as well.
// e.g. If some term already uses "f" as a variable and we add "f : A -> B".

// The constructor is private -- the only way to make theories outside of this class
// is through the empty and withXYZ methods 
case class Theory private (signature: Signature, axioms: Set[Term]) {
    
    /** Returns a theory consisting of the current theory but with the given
      * axiom added. Note that this does not modify the current Theory object,
      * but rather just returns a new Theory object. Throws an exception
      * if the result fails to typecheck with respect to this theory's signature.
      */
    def withAxiom(axiom: Term): Theory = {
        val sanitizedAxiom: Term = sanitizeAxiom(axiom)
        Theory(signature, axioms + sanitizedAxiom)
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
        Theory(signature, axioms ++ sanitizedAxioms)
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
    
    def withEnumSort(t: Sort, values: Seq[EnumValue]): Theory = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), axioms)
    }
    
    @varargs
    def withEnumSort(t: Sort, values: EnumValue*): Theory = withEnumSort(t, values.toList)
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO consistency checking
        Theory(signature.withEnumSort(t, values), axioms)
    }

    /** Given an interpretation, return whether it satisfies all axioms of the original theory
      */
    def verifyInterpretation(interpretation: Interpretation): Boolean = {
        // Some Terms are guaranteed to take in only Bools as args (by the typechecker?)
        // eg. and, or. We assume that the input will be only Top/Bottom and convert to a Scala Boolean.
        def forceTermToBool(term: Term): Boolean = term match{
            case Top => true
            case Bottom => false
            case _ => ???
        }
        def boolToTerm(b: Boolean): Term = if(b) Top else Bottom

        // Converts Var to AnnotatedVar based on the constants in the theory's signature
        val varToAnnotated: Map[Var, AnnotatedVar] = signature.constants.map(
            annotatedVar => annotatedVar.variable -> annotatedVar
        ).toMap

        // TODO maybe coalesce into object for all interpretations
        val context: Map[Var, ListBuffer[Term]] = interpretation.constantInterpretations.map{
            case (key, value) => (key.variable, ListBuffer[Term](value))
        }.withDefaultValue(ListBuffer[Term]())

        def appInterpretations(fnName: String, args: Seq[Term]): Term = {
            // This assumes the args are all Vars which can be converted into AnnotatedVars
            // (probably untrue, eg Bool, but need more data)
            val argsInterpretation = args.map(a => context(a.asInstanceOf[Var]).head)
            // Retrieve FuncDecl signature from the theory, to index the interpretation
            // Assumes there will only be one FuncDecl with a given function name (should be safe)
            val fnSignature = signature.functionDeclarations.filter(fd => fd.name == fnName).head
            val fnInterpretation = interpretation.functionInterpretations(fnSignature)
            // Below type conversion is a lil sketch
            fnInterpretation(argsInterpretation.asInstanceOf[Seq[Value]])
        }

        def evaluate(term: Term): Term = term match{
            // Top/Bottom are "atomic" terms
            // We also treat EnumValues as "atomic" terms (not 100% sure on this)
            case Top | Bottom | EnumValue(_) => term
            case DomainElement(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
            // Is there a better way than asInstanceOf since we already know it's a Var?
            // Translates the variable **BY STRING NAME** to its interpretation (EnumValue or Boolean for now)
            case Var(x) => evaluate(context(term.asInstanceOf[Var]).head)
            // Since we know not/and/or *should* only take in (eventual) Booleans as arguments,
            // can we just use eval().right.get? Does the type checker stop invalid forms?
            case Not(p) => boolToTerm(!forceTermToBool(evaluate(p)))
            case AndList(args) => {
                for(arg <- args){
                    if(!forceTermToBool(evaluate(arg))){
                        return Bottom
                    }
                }
                Top
            }
            case OrList(args) => {
                for(arg <- args){
                    if(forceTermToBool(evaluate(arg))){
                        return Top
                    }
                }
                Bottom
            }
            case Distinct(args) => boolToTerm(
                args.size ==
                args.map(a => context(a.asInstanceOf[Var]).head).distinct.size
            )
            case Implication(p, q) => boolToTerm(
                !forceTermToBool(evaluate(p)) || forceTermToBool(evaluate(q))
            )
            case Iff(p, q) => boolToTerm(
                forceTermToBool(evaluate(p)) == forceTermToBool(evaluate(q))
            )
            // This should be either an equality of EnumValues or equality of Top/Bottom
            // Since these are case classes, equality checks should work as expected
            case Eq(l, r) => boolToTerm(evaluate(l) == evaluate(r))
            case App(fname, args) => appInterpretations(fname, args)
            case BuiltinApp(fname, args) => ???
            case Forall(vars, body) => {
                // TODO assuming one var for now
                // generate a list of all possible values for the var (in this case EnumValues)
                val possibleValues = signature.enumConstants(vars.head.sort)
                for(value <- possibleValues){
                    value +=: context(vars.head.variable)
                    val res = forceTermToBool(evaluate(body))
                    context(vars.head.variable).remove(0)
                    if(!res){
                        return Bottom
                    }
                }
                Top
            }
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
    
    def withoutAxioms: Theory = Theory(signature, Set.empty)
    
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
    def empty: Theory = Theory(Signature.empty, Set.empty)
    
    def mkTheoryWithSignature(signature: Signature): Theory = Theory(signature, Set.empty)
}
