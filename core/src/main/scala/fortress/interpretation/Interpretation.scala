package fortress.interpretation

import scala.collection.mutable
import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations._
import fortress.sortinference._
import fortress.msfol.DSL._
import fortress.solverinterface.Z3NonIncCliSolver
import fortress.util.{ArgumentListGenerator, Errors, Milliseconds}

/** An interpretation of a first-order logic signature. */
trait Interpretation {

    /** Maps a sort to a sequence of values. */
    def sortInterpretations: Map[Sort, Seq[Value]]

    /** Maps a constant symbol to a value. */
    def constantInterpretations: Map[AnnotatedVar, Value]

    /** Maps a function symbol to a mathematical function.
      * The function is represented as a Map itself.
      */
    def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map.empty

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
            case IntLE | IntLT | IntGE | IntGT |
                 BvSignedLE | BvSignedLT | BvSignedGE | BvSignedGT => evalResult of Sort.Bool
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
            functionInterpretations.map{ case(fdecl, values) => fdecl -> (values.map{
                case(args, value) => (args map applyMapping) -> applyMapping(value) }
            )},
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
                mapping map {
                    case(args, value) => (args map apply) -> apply(value)
                }
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
      */
    def toConstraints: Set[Term] = {
        val constraints: mutable.Set[Term] = mutable.Set.empty
        
        for((const, v) <- constantInterpretations) {
            constraints += (const.variable === v)
        }
        
        for {
            (fdecl, map) <- functionInterpretations
            (arguments, value) <- map
        } {
            fdecl.resultSort match {
                case BoolSort => { // Predicate
                    if(value == Top) constraints += App(fdecl.name, arguments)
                    else constraints += Not(App(fdecl.name, arguments))
                }
                case _ =>  { // Function
                    constraints += (App(fdecl.name, arguments) === value)
                }
            }
        }
        constraints.toSet
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
    
    def functionInterpretationsJava: java.util.Map[FuncDecl, java.util.Map[java.util.List[Value], Value]] = functionInterpretations.map {
        case (fdecl, values) => fdecl -> (values.map {
            case (args, ret) => args.asJava -> ret
        }).asJava
    }.asJava
    
    def constantInterpretationsJava: java.util.Map[AnnotatedVar, Value] = constantInterpretations.asJava
    
    def sortInterpretationsJava: java.util.Map[Sort, java.util.List[Value]] = sortInterpretations.map {
        case (sort, values) => sort -> values.asJava
    }.asJava
}
