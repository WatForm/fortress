package fortress.interpretation

import fortress.tfol._
import fortress.data.CartesianProduct

import scala.collection.immutable.ListMap
import scala.collection.JavaConverters._

import com.microsoft.z3._

class Z3ApiInterpretation(model: Model, sig: Signature, typeMappings: Map[Expr, DomainElement]) extends Interpretation {

    def this(model: Model, sig: Signature) = this(model, sig, (
        for {
            z3Decl <- model.getConstDecls
            constantName = z3Decl.getName.toString if constantName.charAt(0) == '@'
        } yield {
            val typeName = z3Decl.getRange.getName.toString
            model.getConstInterp(z3Decl) -> Term.mkDomainElement(constantName.substring(1,constantName.length-typeName.length).toInt, Type.mkTypeConst(typeName))
        }
    ).toMap)

    var constantInterpretations: Map[AnnotatedVar, Value] = (
        for {
            z3Decl <- model.getConstDecls
            v = sig.queryConstant(Term.mkVar(z3Decl.getName.toString)) if v.isDefined
        } yield v.get -> typeMappings(model.getConstInterp(z3Decl))
    ).toMap

    var typeInterpretations: Map[Type, Seq[Value]] = (
        for {
            sort <- model.getSorts
            t = Type.mkTypeConst(sort.getName.toString) if sig.hasType(t) 
        } yield t -> ((1 to model.getSortUniverse(sort).length) map { Term.mkDomainElement(_,t) })
    ).toMap

    var functionInterpretations: Map[fortress.tfol.FuncDecl, ListMap[Seq[Value], Value]] = (
        for {
            z3Decl <- model.getFuncDecls
            fdecl = sig.queryUninterpretedFunction(z3Decl.getName.toString) if fdecl.isDefined
        } yield fdecl.get -> {
            val seqOfDomainSeqs = fdecl.get.argTypes.map (sort => typeInterpretations(sort).asJava).asJava
            val argumentLists = new CartesianProduct[Value](seqOfDomainSeqs)
            val inverseTypeMappings: Map[Value, Expr] = typeMappings.map(_.swap)
            var argumentMapping: ListMap[Seq[Value], Value] = ListMap.empty
            argumentLists.forEach (args => {
                val returnExpr = model.evaluate(z3Decl.apply(args.asScala.map(a => inverseTypeMappings(a)):_*), true)
                var v: Value = Term.mkTop
                if (z3Decl.getRange.isInstanceOf[BoolSort])
                    v = if (returnExpr.isTrue) Term.mkTop else Term.mkBottom
                else
                    v = typeMappings(returnExpr)
                argumentMapping += (args.asScala -> v)
            })
            argumentMapping
        }
    ).toMap
}
