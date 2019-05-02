package fortress.interpretation

import scala.collection.JavaConverters._

import fortress.tfol._

trait Interpretation {
    def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]
    def constantInterpretations: Map[AnnotatedVar, Value]
    def typeInterpretations: Map[Type, Seq[Value]]

    def viewModel(enumMapping: Var => DomainElement): Interpretation = {
        ???
    }

    def toConstraints: Set[Term] = {
        var constraints = constantInterpretations.map{ case(a, v) => Term.mkEq(a.getVar, v) }.toSet
        functionInterpretations.foreach { case(fdecl, values) => {
            fdecl.getResultType match {
                case Type.Bool => constraints = constraints union values.map{ case(args, ret) => if (ret == Term.mkTop) Term.mkApp(fdecl.getName, args:_*) else Term.mkNot(Term.mkApp(fdecl.getName, args:_*))}.toSet
                case _ => constraints = constraints union values.map{ case(args, ret) => Term.mkEq(Term.mkApp(fdecl.getName, args:_*), ret)}.toSet
            }
        }}
        constraints
    }

    override def toString: String = "Types <<\n" + typeInterpretations.map{ case(sort, values) => sort + ": " + values.mkString(", ")}.mkString("\n") + ">>\nConstants <<\n" + constantInterpretations.map(_.productIterator.mkString(": ")).mkString("\n") + ">>\nFunctions <<\n" + functionInterpretations.map{ case(fdecl, values) => fdecl + "\n" + values.map{ case(args, ret) => "\t" + args.mkString(", ") + " -> " + ret }.mkString("\n") }.mkString("\n") + ">>"
    
    // Java methods
    
    def functionInterpretationsJava: java.util.Map[FuncDecl, java.util.Map[java.util.List[Value], Value]] = functionInterpretations.map {
        case (fdecl, values) => fdecl -> (values.map {
            case (args, ret) => args.asJava -> ret
        }).asJava
    }.asJava
    
    def constantInterpretationsJava: java.util.Map[AnnotatedVar, Value] = constantInterpretations.asJava
    
    def typeInterpretationsJava: java.util.Map[Type, java.util.List[Value]] = typeInterpretations.map {
        case (sort, values) => sort -> values.asJava
    }.asJava
    
}
