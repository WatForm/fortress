package fortress.interpretation

import scala.jdk.CollectionConverters._

import scala.collection.immutable.Seq

import fortress.msfol._

trait Interpretation {
    def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
    def constantInterpretations: Map[AnnotatedVar, Value]
    def sortInterpretations: Map[Sort, Seq[Value]]

    def viewModel(enumMapping: Map[Value, EnumValue]): Interpretation = {
        def getMapping(v: Value): Value = if (enumMapping.contains(v)) enumMapping(v) else v
        new EnumInterpretation(
            sortInterpretations.map{ case(sort, values) => sort -> values.map(getMapping) }, 
            constantInterpretations.map{ case(av, value) => av -> getMapping(value) }, 
            functionInterpretations.map{ case(fdecl, values) => fdecl -> (values.map{ 
                case(args, values) => args.map(getMapping) -> getMapping(values) } 
            )}
        )
    }

    def toConstraints: Set[Term] = {
        var constraints = constantInterpretations.map{ case(a, v) => Term.mkEq(a.variable, v) }.toSet
        functionInterpretations.foreach { case(fdecl, values) => {
            fdecl.resultSort match {
                case Sort.Bool => constraints = constraints union values.map{ case(args, ret) => if (ret == Term.mkTop) Term.mkApp(fdecl.name, args:_*) else Term.mkNot(Term.mkApp(fdecl.name, args:_*))}.toSet
                case _ => constraints = constraints union values.map{ case(args, ret) => Term.mkEq(Term.mkApp(fdecl.name, args:_*), ret)}.toSet
            }
        }}
        constraints
    }

    override def toString: String =
        "Sorts <<\n" + sortInterpretations.map{ case(sort, values) => sort.toString + ": " + values.mkString(", ")}.mkString("\n") +
        ">>\nConstants <<\n" + constantInterpretations.map(_.productIterator.mkString(": ")).mkString("\n") +
        ">>\nFunctions <<\n" + functionInterpretations.map{ case(fdecl, values) => fdecl.toString + "\n" + values.map{ case(args, ret) => "\t" + args.mkString(", ") + " -> " + ret }.mkString("\n") }.mkString("\n") +
        ">>"
    
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

class EnumInterpretation(t: Map[Sort, Seq[Value]], c: Map[AnnotatedVar, Value], f: Map[FuncDecl, Map[Seq[Value], Value]]) extends Interpretation {
    def sortInterpretations = t
    def constantInterpretations = c
    def functionInterpretations = f
}

class BasicInterpretation(
    val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]],
    val constantInterpretations: Map[AnnotatedVar, Value],
    val sortInterpretations: Map[Sort, Seq[Value]]
) extends Interpretation
