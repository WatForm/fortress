package fortress.interpretation

import scala.jdk.CollectionConverters._

import fortress.msfol._
import scala.collection.mutable

trait Interpretation {
    def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
    def constantInterpretations: Map[AnnotatedVar, Value]
    def sortInterpretations: Map[Sort, Seq[Value]]

    def applyEnumMapping(enumMapping: Map[Value, EnumValue]): Interpretation = {
        def applyMapping(v: Value): Value = if (enumMapping contains v) enumMapping(v) else v
        
        new BasicInterpretation(
            sortInterpretations.map{ case(sort, values) => sort -> (values map applyMapping) }, 
            constantInterpretations.map{ case(av, value) => av -> applyMapping(value) }, 
            functionInterpretations.map{ case(fdecl, values) => fdecl -> (values.map{ 
                case(args, value) => (args map applyMapping) -> applyMapping(value) } 
            )}
        )
    }

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
