package fortress.interpretation

import scala.collection.mutable
import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations._
import fortress.sortinference._
import fortress.msfol.DSL._
import fortress.solvers.Z3NonIncCliSolver
import fortress.util.{ArgumentListGenerator, Errors, Milliseconds, SmartEq}
import fortress.util.NameConverter.nameWithQuote

/** An interpretation of a first-order logic signature. */
trait Interpretation {

    /** Maps a sort to a sequence of values. */
    def sortInterpretations: Map[Sort, Seq[Value]]

    /** Maps a constant symbol to a value. */
    def constantInterpretations: Map[AnnotatedVar, Value]

    /** Maps a function symbol to a mathematical function.
      * The function is represented as a Map itself.
      */
    def functionInterpretations: Map[FuncDecl, FunctionInterpretation] = Map.empty

    def functionDefinitions: Set[FunctionDefinition]



    def forceValueToBool(term: Value): Boolean = term match{
        case Top => true
        case Bottom => false
        case _ => Errors.Internal.impossibleState("Tried to cast non-Top/Bottom Term to Boolean")
    }

    def boolToValue(b: Boolean): Value = if(b) Top else Bottom


    def getFunctionValue(fnName: String, evaluatedArgs: Seq[Value]): Value = {
        val funcDef = functionDefinitions.filter(fd => fd.name == fnName).head
        val formalArgs: Seq[Term] = for( item <- funcDef.argSortedVar ) yield item.variable
        // transfer constants to domain elements, ex: p1 -> _@1P
        val realArgs: Seq[Value] = for( item <- evaluatedArgs ) yield {
            var temp: Value = item
            // TODO: look here! @zxt
            //                for( a <- instance.constantInterpretations ) {
            //                    if(a._1.variable.name == temp.toString ) temp = a._2
            //                }
            temp
        }
        val body = funcDef.body
        Errors.Internal.precondition(evaluatedArgs.size == formalArgs.size, "Invalid input params.")
        val argMap: Map[Term, Value] = formalArgs.zip(realArgs).toMap
        val ret: Value = visitFunctionBody( body, argMap )
        ret
    }

    def visitFunctionBody(term: Term, argMap: Map[Term, Value]): Value = term match {
        case Top | Bottom | EnumValue(_) | DomainElement(_, _) |
             IntegerLiteral(_) | BitVectorLiteral(_, _) => term.asInstanceOf[Value]
        case v @ Var(_) => argMap(v)
        case Not(p) => boolToValue(!forceValueToBool(visitFunctionBody(p, argMap)))
        case AndList(args) => boolToValue(args.forall(a => forceValueToBool(visitFunctionBody(a, argMap))))
        case OrList(args) => boolToValue(args.exists(a => forceValueToBool(visitFunctionBody(a, argMap))))
        case Distinct(args) => boolToValue(
            args.size == args.map(a => visitFunctionBody(a, argMap)).distinct.size
        )
        case Implication(p, q) => boolToValue(
            !forceValueToBool(visitFunctionBody(p, argMap)) || forceValueToBool(visitFunctionBody(q, argMap))
        )
        case Iff(p, q) => boolToValue(
            forceValueToBool(visitFunctionBody(p, argMap)) == forceValueToBool(visitFunctionBody(q, argMap))
        )
        case Eq(l, r) => boolToValue(visitFunctionBody(l, argMap) == visitFunctionBody(r, argMap))
        case IfThenElse(condition, ifTrue, ifFalse) => {
            if(forceValueToBool(visitFunctionBody(condition, argMap))) {
                visitFunctionBody(ifTrue, argMap)
            }
            else {
                visitFunctionBody(ifFalse, argMap)
            }
        }
        case App(fname, args) => getFunctionValue(fname, args.map(arg => visitFunctionBody(arg, argMap)))
        case BuiltinApp(fn, args) => evaluateBuiltIn(fn, args.map(arg => visitFunctionBody(arg, argMap)))
        case _ => {
            println("Error: get function value failed.")
            null
        }
    }

    // Given a term and a set of free variables, find the set of assignments of values to the free variables
    // in this interpretation that make the term equal to outputValue.
    // See PreimageFinding for more information.
    def findPreimage(vars: Seq[AnnotatedVar], term: Term, outputValue: Value): Set[Seq[Value]] =
        PreimageFinding.findPreimage(this, vars, term, outputValue)

    // Given a builtin function and its arguments, run it through a throwaway Z3 solver for the result
    // (to avoid having to implement every function manually on our end)
    def evaluateBuiltIn(fn: BuiltinFunction, evalArgs: Seq[Value]): Value = {
        val evalResult: Var = Var("!VERIFY_INTERPRETATION_RES")
        var isBv2Int = false // Ints are converted SIGNED, we want unsigned
        val evalResultAnnotated: AnnotatedVar = fn match {
            case IntPlus | IntNeg | IntSub | IntMult | IntDiv | IntMod => evalResult of Sort.Int
            case BvPlus | BvNeg | BvSub | BvMult | BvSignedDiv | BvSignedRem | BvSignedMod =>
                evalResult of Sort.BitVector(evalArgs.head.asInstanceOf[BitVectorLiteral].bitwidth);
            case IntLE | IntLT | IntGE | IntGT | IntEQ |
                 BvSignedLE | BvSignedLT | BvSignedGE | BvSignedGT | BvEQ => evalResult of Sort.Bool
            case CastBVToInt => {
                isBv2Int = true
                evalResult of Sort.Int
            }
            case CastIntToBV(bitwidth) => evalResult of BitVectorSort(bitwidth)
            case _ => throw new scala.NotImplementedError("Builtin function not accounted for")
        }

        // Early handling of Bv2Int casting
        if (isBv2Int){
            val signedBV = evalArgs.head.asInstanceOf[BitVectorLiteral].signed
            return IntegerLiteral(signedBV.value)
            
        }

        val theory: Theory = Theory.empty
                .withConstantDeclaration(evalResultAnnotated)
                .withAxiom(evalResult === BuiltinApp(fn, evalArgs))
        
        val solver = new Z3NonIncCliSolver
        solver.setTheory(theory)
        solver.solve(Milliseconds(1000))
        val solvedInstance = solver.solution
        solver.close()

        solvedInstance.constantInterpretations(evalResultAnnotated)
    }


    /** Replaces the Values of an interpretation EnumValues, according to the given substitution map.
     * Useful for undoing Enum Elimination.
     */
    def replaceValuesWithEnums(enumMapping: Map[Value, EnumValue]): Interpretation = {

        def applyMapping(v: Value): Value = if (enumMapping contains v) enumMapping(v) else v

        def visitBody(term: Term): Term = term match {
            case AndList(args) => AndList(args.map(visitBody))
            case OrList(args) => OrList(args.map(visitBody))
            case (distinct: Distinct) => visitBody(distinct.asPairwiseNotEquals)
            case Implication(left, right) => Implication(visitBody(left), visitBody(right))
            case Iff(p, q) => Iff(visitBody(p), visitBody(q))
            case Forall(vars, body) => Forall(vars, visitBody(body))
            case Exists(vars, body) => Exists(vars, visitBody(body))
            case Not(body) => Not(visitBody(body))
            case App(name, args) => App(name, args.map(visitBody))
            case Closure(name, arg1, arg2, fixedArgs) => Closure(name, visitBody(arg1), visitBody(arg2), fixedArgs.map(visitBody))
            case ReflexiveClosure(name, arg1, arg2, fixedArgs) => ReflexiveClosure(name, visitBody(arg1), visitBody(arg2), fixedArgs.map(visitBody))
            case Eq(p, q) => Eq(visitBody(p), visitBody(q))
            case DomainElement(index, sort) => {
                val t: Value = term.asInstanceOf[Value]
                applyMapping(t)
            }
            case IfThenElse(a, b, c) => IfThenElse(visitBody(a), visitBody(b), visitBody(c))
            case _ => term
        }
        
        new BasicInterpretation(
            sortInterpretations.map{ case(sort, values) => sort -> (values map applyMapping) }, 
            constantInterpretations.map{ case(av, value) => av -> applyMapping(value) },
            functionInterpretations.map{ case(fdecl, interp) => fdecl -> interp.replaceValuesWithEnums(enumMapping)},
            functionDefinitions.map{ case functionDefinition: FunctionDefinition => {
                // visit the funcBody term, replace the values with enum
                val name: String = functionDefinition.name
                val vars: Seq[AnnotatedVar] = functionDefinition.argSortedVar
                val resultSort = functionDefinition.resultSort
                val newBody: Term = visitBody(functionDefinition.body)
                new FunctionDefinition(name, vars, resultSort, newBody)
            } }
        )
    }
    
    /** Replaces the sorts of the Values in the interpretation according to the given substitution.
      * Useful for undoing sort inference.
      */
    def applySortSubstitution(sub: SortSubstitution): Interpretation = {
        val apply: Value => Value = v => sub.applyValue(v)
        val newSortInterps = sortInterpretations map {
            case(sort, values) => sub(sort) -> (values map apply)
        }
        val newConstInterps = constantInterpretations map {
            case(const, value) => sub(const) -> apply(value)
        }
        val newFunctionInterps = functionInterpretations map {
            case(fdecl, mapping) => sub(fdecl) -> {
                mapping.applySortSubstitution(sub)
            }
        }
        val newFunctionDefinitions = functionDefinitions map sub.apply
        // TODO: what to do on functionDefinitions
        new BasicInterpretation(newSortInterps, newConstInterps, newFunctionInterps, newFunctionDefinitions)
    }
    
    /** Shows only the parts of the interpretation which are in the given signature. */
    def filterBySignature(signature: Signature): Interpretation = {
        val newSortInterps = sortInterpretations filter { case(sort, values) => signature hasSort sort }
        val newConstInterps = constantInterpretations filter { case(const, value) => signature.constantDeclarations contains const }
        val newFunctionInterps = functionInterpretations filter {case(fdecl, mapping) => signature.functionDeclarations contains fdecl }
        val newFunctionDefinitions = functionDefinitions filter { fd => {
            for( item <- signature.functionDeclarations ) {
                if( item.name == fd.name ) true
            }
            false
        } }
        new BasicInterpretation(newSortInterps, newConstInterps, newFunctionInterps, newFunctionDefinitions)
    }

    /** Removes the given declarations from the interpretation. */
    def withoutDeclarations(decls: Set[Declaration]): Interpretation = {
        def castConstant(decl: Declaration): Option[AnnotatedVar] = decl match {
            case c: AnnotatedVar => Some(c)
            case f: FuncDecl => None
        }

        def castFuncDecl(decl: Declaration): Option[FuncDecl] = decl match {
            case c: AnnotatedVar => None
            case f: FuncDecl => Some(f)
        }

        val constants: Set[AnnotatedVar] = decls.map(castConstant).flatten
        val fdecls: Set[FuncDecl] = decls.map(castFuncDecl).flatten

        this.withoutConstants(constants).withoutFunctions(fdecls)
    }
    
    /** Removes the given constants from the interpretation. */
    def withoutConstants(constants: Set[AnnotatedVar]): Interpretation = {
        new BasicInterpretation(
            sortInterpretations,
            constantInterpretations -- constants,
            functionInterpretations,
            functionDefinitions
        )
    }

    /** Removes the given definitions from the interpretation */
    def withoutFunctionDefinitions(definitions: Set[FunctionDefinition]): Interpretation = {
        new BasicInterpretation(
            sortInterpretations,
            constantInterpretations,
            functionInterpretations,
            functionDefinitions -- definitions
        )
    }
    
    /** Removes the given functions from the interpretation. */
    def withoutFunctions(funcDecls: Set[FuncDecl]): Interpretation = {
        val newFunctionDefinitions: Set[FunctionDefinition] = functionDefinitions.filter(item => {
            var flag = true
            for(fd <- funcDecls) {
                if(fd.name == item.name) flag = false
            }
            flag
        })

        new BasicInterpretation(
            sortInterpretations,
            constantInterpretations,
            functionInterpretations -- funcDecls,
            newFunctionDefinitions
        )
    }

    /** Updates the Interpretation to drop the specified sort */
    def withoutSorts(sorts:Set[Sort]): Interpretation = {
        new BasicInterpretation(
            sortInterpretations -- sorts,
            constantInterpretations,
            functionInterpretations,
            functionDefinitions
        )
    }

    /** Updates thr domain elements associated with specified sort. */
    def updateSortInterpretations(sort: Sort, values: Seq[Value]): Interpretation = {
        new BasicInterpretation(
            sortInterpretations + (sort -> values),
            constantInterpretations,
            functionInterpretations,
            functionDefinitions
        )
    }

    /** Generates a set of constraints which says that an interpretation must agree
      * with this interpretation on all of the constants and functions present.
      * 
      * When fixing "nextInterpretation", we should only include constraints for
      * functions in the theory.
      * Not even universe constraints (?) 
      */
    def constraintAxioms: Seq[Term] = {
        // Order is important because values must be declared before use
        val constraints: mutable.Buffer[Term] = mutable.Buffer.empty
        
        // Add constraints for scopes of sorts
        constraints ++= universeConstraints

        // Constant Interpretations
        for((const, v) <- constantInterpretations) {
            constraints += (const.variable === v)
        }
        
        // Function Interpretations
        for {
            (fdecl, finterp) <- functionInterpretations
        } {
            constraints ++= finterp generateConstraints fdecl
        }

        // Function Definitions
        for {(fDef) <- functionDefinitions} {
            // Function may be nullary so we add this check
            if (fDef.argSortedVar.size == 0){
                Eq(Var(fDef.name), fDef.body)
            } else {
                // Axiomatize the function
                constraints += Forall(fDef.argSortedVar, Eq(
                    App(fDef.name, fDef.argSortedVar.map(_.variable)), fDef.body
                    )
                )
            }
            
        }

        constraints.toSeq
    }

    def SMTConstraints(initialTheory: Theory): String = {
        val output = new StringBuilder()

            sortInterpretations.foreach({case (sort, values) => {
            if (!sort.isBuiltin) { // Don't declare constants for builtins
                values.foreach(value => value match {
                    case de: DomainElement => {
                        output.append(f"(declare-const ${de.asSmtConstant} ${sort.name})\n")
                    }
                    case ev: EnumValue => () // Enum Values should be already included (probably)
                    // Not sure why BVLiteral can't be used as a type here, but it seems fine on the left
                    case  BitVectorLiteral(_,_) => Errors.Internal.impossibleState(f"Should not be trying to declare smtlib builtin: ${value}")
                    case _ : IntegerLiteral | Top | Bottom => Errors.Internal.impossibleState(f"Should not be trying to declare smtlib builtin: ${value}")
                })
                // Range restrictions are below

                output.append('\n')
            }
        }})
        val sig = initialTheory.signature
        // Declare functions that do not appear in the theory
        for {(fDef) <- functionDefinitions.filter(f => !sig.hasFuncWithName(f.name))} {
            // Constants can be in here due to weird parsing stuff
            if (fDef.argSorts.size == 0){
                // Only declare them if they haven't already been declared
                if (!sig.hasConstDeclWithName(fDef.name)){
                    output.append(f"(declare-const ${nameWithQuote(fDef.name)}  ${nameWithQuote(fDef.resultSort.name)})\n")
                }
            } else {
                output.append("(declare-func ")
                output.append(nameWithQuote(fDef.name))
                // Args
                output.append("(")
                output.append(fDef.argSorts.map(f => nameWithQuote(f.name)).mkString(" "))
                output.append(") ")

                output.append(nameWithQuote(fDef.resultSort.name))
                output.append(")\n")
            }
        }

        // Print the constraints
        for (axiom <- constraintAxioms){
            output.append(TermOps(axiom).smtlibAssertionWithDEs)
        }
        
        output.result()
    }

    def universeConstraints: Seq[Term] = {
        val elem = Var("elem")
        val constraints: mutable.Buffer[Term] = mutable.Buffer.empty
        sortInterpretations.foreach({
            case (sort, values) =>
                
            sort match {
                case IntSort | BitVectorSort(_) | BoolSort => ()
                case _ => // forall elem: Sort. sort=value1 || sort=value2 ...
                constraints :+ (Forall(elem.of(sort), Or.smart(
                    values.map(value=> SmartEq.smartEq(sort, elem, value))
                )))
            }   
        })

        constraints.toSeq
    }

    override def toString: String = {
        val buffer = new mutable.StringBuilder

        buffer ++= "+------------------------------View Model------------------------------+\n"

        if(sortInterpretations.nonEmpty) {
            buffer ++= "\nSorts:\n"
            val sortLines = for((sort, values) <- sortInterpretations) yield {
                sort.toString + ": " + values.mkString(", ")
            }
            buffer ++= sortLines.mkString("\n")
        }

        if(constantInterpretations.nonEmpty) {
            buffer ++= "\n\nConstants: \n"
            val constLines = for((const, value) <- constantInterpretations) yield {
                const.toString + " = " + value.toString
            }
            buffer ++= constLines.mkString("\n")
            buffer ++= "\n"
        }

        if(functionDefinitions.nonEmpty) {
            buffer ++= "\nFunction Definitions:\n"
            for( item <- functionDefinitions) {
                buffer ++= item.toString
            }
        }

//        if(functionInterpretations.nonEmpty) {
//            buffer ++= "\nFunctions values: "
//            for {
//                (fdecl, map) <- functionInterpretations
//            } {
//                buffer ++= "\n" + fdecl.toString + "\n"
//                val argLines = for((arguments, value) <- map) yield {
//                    fdecl.name + "(" + arguments.mkString(", ") + ") = " + value.toString
//                }
//                buffer ++= argLines.mkString("\n")
//            }
//        }

        buffer ++= "+----------------------------------------------------------------------+\n"

        buffer.toString
    }
    
    // Java methods
    
    def functionInterpretationsJava: java.util.Map[FuncDecl, FunctionInterpretation] = functionInterpretations.map {
        case (fdecl, interp) => fdecl -> interp
    }.asJava
    
    def constantInterpretationsJava: java.util.Map[AnnotatedVar, Value] = constantInterpretations.asJava
    
    def sortInterpretationsJava: java.util.Map[Sort, java.util.List[Value]] = sortInterpretations.map {
        case (sort, values) => sort -> values.asJava
    }.asJava
}
