package fortress.msfol

import java.io.StringWriter

import fortress.data.CartesianSeqProduct
import fortress.interpretation.Interpretation
import fortress.msfol
import fortress.util.Errors
import fortress.msfol.operations.TypeCheckResult
import fortress.solverinterface.SolverStrategy
import fortress.solverinterface.Z3ApiSolver
import fortress.util.Errors.AssertionException

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

    /** Given an interpretation, test & return whether it satisfies all axioms of the original theory
      */
    def verifyInterpretation(interpretation: Interpretation): Boolean = {
        // Utility functions to transform between Scala Booleans and Fortress ones
        def forceTermToBool(term: Term): Boolean = term match{
            case Top => true
            case Bottom => false
            case _ => throw new AssertionException("Tried to cast non-Top/Bottom Term to Boolean")
        }
        def boolToTerm(b: Boolean): Term = if(b) Top else Bottom

        // Context: A mapping of Vars to ListBuffer[Term]s (used as a stack).
        // The head of the ListBuffer will always hold the innermost binding of the Var,
        // with the "default" context being the base interpretation itself.
        val context: scala.collection.mutable.Map[Var, ListBuffer[Term]] =
            scala.collection.mutable.Map() ++ interpretation.constantInterpretations.map{
                // We convert from AnnotatedVar to Var (safe since names are distinct)
                // and Value to Term (widening conversion)
                case (key, value) => (key.variable, ListBuffer[Term](value))
            }
        def pushToContext(key: Var, value: Term): Unit = {
            if(context.contains(key)) value +=: context(key)
            else context(key) = ListBuffer[Term](value)
        }
        def popFromContext(key: Var): Unit = {
            if(context(key).length == 1) context -= key
            else context(key).remove(0)
        }

        // Given a function and its arguments, look inside the interpretation to find the result
        def appInterpretations(fnName: String, evaluatedArgs: Seq[Term]): Term = {
            // Retrieve FuncDecl signature from the theory (used to index the interpretation)
            val fnSignature = signature.functionDeclarations.filter(fd => fd.name == fnName).head
            val fnInterpretation = interpretation.functionInterpretations(fnSignature)
            // Below type conversion is a lil sketch (narrowing conversion?)
            fnInterpretation(evaluatedArgs.asInstanceOf[Seq[Value]])
        }

        // Given a builtin function and its arguments, run it through a throwaway Z3 solver for the result
        // (to avoid having to implement every function manually on our end)
        def evaluateBuiltIn(fn: BuiltinFunction, evalArgs: Seq[Term]): Term = {
            val solver: SolverStrategy = new Z3ApiSolver
            val evalResult: Var = Var("$VERIFY_INTERPRETATION_RES")
            // TODO when we see a BV function, annotate with Sort.BitVector(bw)
            val evalResultAnnotated: AnnotatedVar = fn match{
                case IntPlus | IntNeg | IntSub | IntMult | IntDiv | IntMod => evalResult of Sort.Int
                case BvPlus | BvNeg | BvSub | BvMult | BvSignedDiv | BvSignedRem | BvSignedMod => ???
                case IntLE | IntLT | IntGE | IntGT |
                     BvSignedLE | BvSignedLT | BvSignedGE | BvSignedGT => evalResult of Sort.Bool
                case _ => throw new scala.NotImplementedError("Builtin function not accounted for")
            }
            val theory: Theory = Theory.empty
                .withConstant(evalResultAnnotated)
                .withAxiom(evalResult === BuiltinApp(fn, evalArgs))
            solver.solve(theory, 1000, new StringWriter)
            val solvedInstance = solver.getInstance(theory)
            solvedInstance.constantInterpretations(evalResultAnnotated)
        }

        // Recursively evaluates a given expression to either Top or Bottom, starting from the root
        def evaluate(term: Term): Term = term match{
            // "Atomic" terms should be maintained as-is
            case Top | Bottom | EnumValue(_) | DomainElement(_, _) |
                 IntegerLiteral(_) | BitVectorLiteral(_, _) => term
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
            // The operands to Eq are expected to be case classes, so equality works as expected
            case Eq(l, r) => boolToTerm(evaluate(l) == evaluate(r))
            case App(fname, args) => appInterpretations(fname, args.map(arg => evaluate(arg)))
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
                        case (value, index) => pushToContext(vars(index).variable, value)
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
                        case (value, index) => pushToContext(vars(index).variable, value)
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
