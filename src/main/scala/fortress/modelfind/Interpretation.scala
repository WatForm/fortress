package fortress.modelfind

import scala.collection.JavaConverters._

import fortress.tfol._

// TODO: change DomainElement to Value
class Interpretation {
    var constantMappings: Map[AnnotatedVar, DomainElement] = Map.empty
    var functionMappings: Map[FuncDecl, Map[java.util.List[DomainElement], DomainElement]] = Map.empty

    def addConstantMapping(v: AnnotatedVar, elem: DomainElement) = constantMappings += (v -> elem)
    def addFunctionMapping(f: FuncDecl, args: java.util.List[DomainElement], ret: DomainElement) = functionMappings += (f -> (functionMappings.getOrElse(f, Map.empty) + (args -> ret)))

    // TODO: change accordingly for Value
    def toConstraint: Term = {
    	Term.mkAnd((constantMappings.map{ case (v, e) => Term.mkEq(v.getVar, e)} ++ functionMappings.map{ case (f, i) => {
    		var retType: Boolean = f.getResultType == Type.Bool
    		Term.mkAnd(i.map{ case (d, r) => if (retType) (if (r == Term.mkDomainElement(2, Type.Bool)) Term.mkApp(f.getName, d) else Term.mkNot(Term.mkApp(f.getName, d))) else Term.mkEq(Term.mkApp(f.getName, d), r) }.toList.asJava) 
    	}}).toList.asJava)
    }

    override def toString: String = "Constants <<\n" + constantMappings.map(_.productIterator.mkString(": ")).mkString("\n") + ">>\nFunctions <<\n" + functionMappings.map(pair => pair._1 + "\n" + pair._2.map(lst => "\t" + java.util.Arrays.toString(lst._1.toArray()) + " -> " + lst._2).mkString("\n")).mkString("\n") + ">>"
}
