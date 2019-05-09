package fortress.interpretation

import fortress.tfol._
import fortress.data.CartesianProduct

import scala.collection.immutable.ListMap
import scala.collection.JavaConverters._

import com.microsoft.z3.{
    Model => Z3Model,
    BoolSort => Z3BoolSort,
    Sort => Z3Sort,
    Expr => Z3Expr
}
    

class Z3ApiInterpretation(model: Z3Model, sig: Signature, sortMappings: Map[Z3Expr, DomainElement]) extends Interpretation {

    def this(model: Z3Model, sig: Signature) = this(model, sig, (
        for {
            z3Decl <- model.getConstDecls
            constantName = z3Decl.getName.toString if constantName.charAt(0) == '@'
        } yield {
            val sortName = z3Decl.getRange.getName.toString
            model.getConstInterp(z3Decl) -> Term.mkDomainElement(constantName.substring(1,constantName.length-sortName.length).toInt, Sort.mkSortConst(sortName))
        }
    ).toMap)

    var constantInterpretations: Map[AnnotatedVar, Value] = (
        for {
            z3Decl <- model.getConstDecls
            v = sig.queryConstant(Term.mkVar(z3Decl.getName.toString)) if v.isDefined
        } yield v.get -> sortMappings(model.getConstInterp(z3Decl))
    ).toMap

    var sortInterpretations: Map[Sort, Seq[Value]] = (
        for {
            sort <- model.getSorts
            t = Sort.mkSortConst(sort.getName.toString) if sig.hasSort(t) 
        } yield t -> ((1 to model.getSortUniverse(sort).length) map { Term.mkDomainElement(_,t) })
    ).toMap

    var functionInterpretations: Map[fortress.tfol.FuncDecl, ListMap[Seq[Value], Value]] = (
        for {
            z3Decl <- model.getFuncDecls
            fdecl = sig.queryUninterpretedFunction(z3Decl.getName.toString) if fdecl.isDefined
        } yield fdecl.get -> {
            val seqOfDomainSeqs = fdecl.get.argSorts.map (sort => sortInterpretations(sort).asJava).asJava
            val argumentLists = new CartesianProduct[Value](seqOfDomainSeqs)
            val inverseSortMappings: Map[Value, Z3Expr] = sortMappings.map(_.swap)
            var argumentMapping: ListMap[Seq[Value], Value] = ListMap.empty
            argumentLists.forEach (args => {
                val returnExpr = model.evaluate(z3Decl.apply(args.asScala.map(a => inverseSortMappings(a)):_*), true)
                var v: Value = Term.mkTop
                if (z3Decl.getRange.isInstanceOf[Z3BoolSort])
                    v = if (returnExpr.isTrue) Term.mkTop else Term.mkBottom
                else
                    v = sortMappings(returnExpr)
                argumentMapping += (args.asScala -> v)
            })
            argumentMapping
        }
    ).toMap
}
