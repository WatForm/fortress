package fortress.interpretation

import scala.collection.JavaConverters._

import fortress.tfol._

trait Interpretation {
    def viewModel(enumMapping: Var => DomainElement): Interpretation
    def toConstraints: Set[Term]
    
    def functionInterpretations: Map[FuncDecl, Seq[Value]]
    def constantInterpretations: Map[AnnotatedVar, Value]
    def typeInterpretations: Map[Type, Seq[Value]]
    
    // Java methods
    
    def functionInterpretationsJava: java.util.Map[FuncDecl, java.util.List[Value]] = functionInterpretations.map {
        case (fdecl, values) => fdecl -> values.asJava
    }.asJava
    
    def constantInterpretationsJava: java.util.Map[AnnotatedVar, Value] = constantInterpretations.asJava
    
    def typeInterpretationsJava: java.util.Map[Type, java.util.List[Value]] = typeInterpretations.map {
        case (sort, values) => sort -> values.asJava
    }.asJava
    
}
