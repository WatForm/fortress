package fortress.interpretation

import scala.collection.mutable
import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations._
import fortress.sortinference._
import fortress.msfol.DSL._
import fortress.util.ArgumentListGenerator

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
        // TODO: what to do on functionDefinitions
        new BasicInterpretation(newSortInterps, newConstInterps, newFunctionInterps, functionDefinitions)
    }
    
    /** Shows only the parts of the interpretation which are in the given signature. */
    def filterBySignature(signature: Signature): Interpretation = {
        val newSortInterps = sortInterpretations filter { case(sort, values) => signature hasSort sort }
        val newConstInterps = constantInterpretations filter { case(const, value) => signature.constants contains const }
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
