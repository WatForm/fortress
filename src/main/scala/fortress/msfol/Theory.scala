package fortress.msfol

import fortress.data.CartesianSeqProduct
import fortress.interpretation.Interpretation
import fortress.util.Errors
import fortress.msfol.operations.TypeCheckResult

import scala.language.implicitConversions
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
        // Some Terms are guaranteed to result in only Top/Bottom (guaranteed by the typechecker?)
        // This function will enforce this assumption and convert to a Scala Boolean
        def forceTermToBool(term: Term): Boolean = term match{
            case Top => true
            case Bottom => false
            case _ => ??? // This case should never be reached (throw error?)
        }
        // Converts a Scala Boolean to Top/Bottom for intermediary steps
        def boolToTerm(b: Boolean): Term = if(b) Top else Bottom

        /** A mapping of Vars to ListBuffer[Term]s (used as a stack).
          * The head of the ListBuffer will always hold the innermost binding of the Var,
          * with the "default" context being the base interpretation itself.
        */
        val context: scala.collection.mutable.Map[Var, ListBuffer[Term]] =
            scala.collection.mutable.Map() ++ interpretation.constantInterpretations.map{
                // We map from AnnotatedVar to Var (safe since names are distinct)
                // and Value to Term (widening conversion)
                case (key, value) => (key.variable, ListBuffer[Term](value))
            }
        def addToContext(key: Var, value: Term): Unit = {
            if(context.contains(key)){
                value +=: context(key)
            }
            else{
                context(key) = ListBuffer[Term](value)
            }
        }
        def popFromContext(key: Var): Unit = {
            if(context(key).length == 1){
                context -= key
            }
            else{
                context(key).remove(0)
            }
        }

        // Given a function, look inside the interpretation to find the result
        def appInterpretations(fnName: String, evaluatedArgs: Seq[Term]): Term = {
            // Retrieve FuncDecl signature from the theory (used to index the interpretation)
            val fnSignature = signature.functionDeclarations.filter(fd => fd.name == fnName).head
            val fnInterpretation = interpretation.functionInterpretations(fnSignature)
            // Below type conversion is a lil sketch (narrowing conversion?)
            fnInterpretation(evaluatedArgs.asInstanceOf[Seq[Value]])
        }

        // Given a builtin function, evaluate it
        def evaluateBuiltIn(fn: BuiltinFunction, evalArgs: Seq[Term]): Term = {
            // Convenience conversions for integer operations
            implicit def forceTermToInt(term: Term): Int = term match{
                case IntegerLiteral(value) => value
                case _ => ???
            }
            implicit def intToTerm(i: Int): Term = IntegerLiteral(i)
            implicit def boolToTerm(b: Boolean): Term = if(b) Top else Bottom

            fn match{
                // Integers
                case IntPlus => evalArgs.head + evalArgs.last
                case IntNeg => -1 * evalArgs.head
                case IntSub => evalArgs.head - evalArgs.last
                case IntMult => evalArgs.head * evalArgs.last
                case IntDiv => evalArgs.head / evalArgs.last
                case IntMod => evalArgs.head % evalArgs.last
                case IntLE => evalArgs.head <= evalArgs.last
                case IntLT => evalArgs.head < evalArgs.last
                case IntGE => evalArgs.head >= evalArgs.last
                case IntGT => evalArgs.head > evalArgs.last
                // Bit vectors
                case BvPlus => ???
                case BvNeg => ???
                case BvSub => ???
                case BvMult => ???
                case BvSignedDiv => ???
                case BvSignedRem => ???
                case BvSignedMod => ???
                case BvSignedLE => ???
                case BvSignedLT => ???
                case BvSignedGE => ???
                case BvSignedGT => ???

                case _ => ???
            }
        }

        // Recursively evaluates a given expression to either Top or Bottom, starting from the root
        def evaluate(term: Term): Term = term match{
            // Top/Bottom are "atomic" terms
            // We also treat EnumValues as "atomic" terms, and may need to do so with more defaults
            case Top | Bottom | EnumValue(_) | DomainElement(_, _) |
                 IntegerLiteral(_) | BitVectorLiteral(_, _) => term
            // TODO ensure this works properly for ints/bitvectors
            case Var(x) => evaluate(context(term.asInstanceOf[Var]).head)
            case Not(p) => boolToTerm(!forceTermToBool(evaluate(p)))
            // And/Or are short circuited
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
            case App(fname, args) => appInterpretations(fname, args.map(arg => evaluate(arg)))
            // The evaluated arguments should only be IntegerLiterals and BitVectorLiterals
            // More testing is needed to ensure this is actually true
            case BuiltinApp(fn, args) => evaluateBuiltIn(fn, args.map(arg => evaluate(arg)))
            case Forall(vars, body) => {
                val varDomains = vars.map(v =>
                    interpretation.sortInterpretations(v.sort).toIndexedSeq
                ).toIndexedSeq
                val allPossibleValueLists = new CartesianSeqProduct[Value](varDomains)
                // Going through all possible combinations of the domain elements:
                // append to the context, recurse, then remove from the context
                for(valueList <- allPossibleValueLists){
                    valueList.zipWithIndex.foreach {
                        case (value, index) => addToContext(vars(index).variable, value)
                    }
                    val res = forceTermToBool(evaluate(body))
                    valueList.zipWithIndex.foreach {
                        case (value, index) => popFromContext(vars(index).variable)
                    }
                    if(!res){
                        return Bottom
                    }
                }
                Top
            }
            case Exists(vars, body) => {
                val varDomains = vars.map(v =>
                    interpretation.sortInterpretations(v.sort).toIndexedSeq
                ).toIndexedSeq
                val allPossibleValueLists = new CartesianSeqProduct[Value](varDomains)
                // Going through all possible combinations of the domain elements:
                // append to the context, recurse, then remove from the context
                for(valueList <- allPossibleValueLists){
                    valueList.zipWithIndex.foreach {
                        case (value, index) => addToContext(vars(index).variable, value)
                    }
                    val res = forceTermToBool(evaluate(body))
                    valueList.zipWithIndex.foreach {
                        case (value, index) => popFromContext(vars(index).variable)
                    }
                    if(res){
                        return Top
                    }
                }
                Bottom
            }
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
