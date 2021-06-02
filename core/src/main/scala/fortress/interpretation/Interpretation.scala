package fortress.interpretation

import scala.collection.mutable
import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.operations._
import fortress.sortinference._
import fortress.msfol.DSL._

/** An interpretation of a first-order logic signature. */
trait Interpretation {

    /** Maps a sort to a sequence of values. */
    def sortInterpretations: Map[Sort, Seq[Value]]

    /** Maps a constant symbol to a value. */
    def constantInterpretations: Map[AnnotatedVar, Value]

    /** Maps a function symbol to a mathematical function.
      * The function is represented as a Map itself.
      */
    def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]

    /** Replaces the Values of an interpretation EnumValues, according to the given substitution map.
     * Useful for undoing Enum Elimination.
     */
    def replaceValuesWithEnums(enumMapping: Map[Value, EnumValue]): Interpretation = {
        def applyMapping(v: Value): Value = if (enumMapping contains v) enumMapping(v) else v
        
        new BasicInterpretation(
            sortInterpretations.map{ case(sort, values) => sort -> (values map applyMapping) }, 
            constantInterpretations.map{ case(av, value) => av -> applyMapping(value) }, 
            functionInterpretations.map{ case(fdecl, values) => fdecl -> (values.map{ 
                case(args, value) => (args map applyMapping) -> applyMapping(value) } 
            )}
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
            case(fdecl, mapping) => fdecl -> {
                mapping map {
                    case(args, value) => (args map apply) -> apply(value)
                }
            }
        }
        new BasicInterpretation(newSortInterps, newConstInterps, newFunctionInterps)
    }
    
    /** Shows only the parts of the interpretation which are in the given signature. */
    def filterBySignature(signature: Signature): Interpretation = {
        val newSortInterps = sortInterpretations filter { case(sort, values) => signature hasSort sort }
        val newConstInterps = constantInterpretations filter { case(const, value) => signature.constants contains const }
        val newFunctionInterps = functionInterpretations filter {case(fdecl, mapping) => signature.functionDeclarations contains fdecl }
        new BasicInterpretation(newSortInterps, newConstInterps, newFunctionInterps)
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
            functionInterpretations
        )
    }
    
    /** Removes the given functions from the interpretation. */
    def withoutFunctions(funcDecls: Set[FuncDecl]): Interpretation = {
        new BasicInterpretation(
            sortInterpretations,
            constantInterpretations,
            functionInterpretations -- funcDecls
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
        
        buffer ++= "Sorts\n"
        
        val sortLines = for((sort, values) <- sortInterpretations) yield {
            sort.toString + ": " + values.mkString(", ")
        }
        buffer ++= sortLines.mkString("\n")
        
        if(constantInterpretations.nonEmpty) {
            buffer ++= "\nConstants\n"
            val constLines = for((const, value) <- constantInterpretations) yield {
                const.toString + " = " + value.toString
            }
            buffer ++= constLines.mkString("\n")
        }
        
        if(functionInterpretations.nonEmpty) {
            buffer ++= "\nFunctions"
            for {
                (fdecl, map) <- functionInterpretations
            } {
                buffer ++= "\n" + fdecl.toString + "\n"
                val argLines = for((arguments, value) <- map) yield {
                    fdecl.name + "(" + arguments.mkString(", ") + ") = " + value.toString
                }
                buffer ++= argLines.mkString("\n")
            }
        }
        
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
