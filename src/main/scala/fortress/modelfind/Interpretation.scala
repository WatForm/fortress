package fortress.modelfind

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import fortress.tfol._

class Interpretation {
    var constantMappings = Map[AnnotatedVar, DomainElement]()
    var functionMappings = Map[FuncDecl, Map[java.util.List[DomainElement], DomainElement]]()

    def addConstantMapping(v: AnnotatedVar, elem: DomainElement) = constantMappings += (v -> elem)
    def addFunctionMapping(f: FuncDecl, args: java.util.List[DomainElement], ret: DomainElement) = functionMappings += (f -> (functionMappings.getOrElse(f, Map[java.util.List[DomainElement], DomainElement]()) + (args -> ret)))

    override def toString: String = "Constants <<\n" + constantMappings.map(_.productIterator.mkString(": ")).mkString("\n") + ">>\nFunctions <<\n" + functionMappings.map(pair => pair._1 + "\n" + pair._2.map(lst => "\t" + java.util.Arrays.toString(lst._1.toArray()) + " -> " + lst._2).mkString("\n")).mkString("\n") + ">>"
}
