package fortress.interpretation

import fortress.msfol._
import fortress.data.CartesianSeqProduct

import scala.collection.immutable.ListMap
import scala.collection.JavaConverters._

import com.microsoft.z3.{
    Model => Z3Model,
    BoolSort => Z3BoolSort,
		IntSort => Z3IntSort,
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
            v = sig.queryConstant(Term.mkVar(z3Decl.getName.toString))
            expr = model.getConstInterp(z3Decl) if v.isDefined
        } yield v.get -> {
            var t: Value = Term.mkTop
            if (z3Decl.getRange.isInstanceOf[Z3BoolSort])
                t = if (expr.isTrue) Term.mkTop else Term.mkBottom
            else if (z3Decl.getRange.isInstanceOf[Z3IntSort])
                t = IntegerLiteral(expr.toString.toInt)
            else
                t = sortMappings(expr)
            t
        }
    ).toMap

    var sortInterpretations: Map[Sort, Seq[Value]] = (
        for {
            z3Sort <- model.getSorts
            t = Sort.mkSortConst(z3Sort.getName.toString) if sig.hasSort(t)
        } yield t -> ((1 to model.getSortUniverse(z3Sort).length) map { Term.mkDomainElement(_,t) })
    ).toMap

    var functionInterpretations: Map[fortress.msfol.FuncDecl, ListMap[Seq[Value], Value]] = (
        for {
            z3Decl <- model.getFuncDecls
            fdecl = sig.queryUninterpretedFunction(z3Decl.getName.toString) if fdecl.isDefined
        } yield fdecl.get -> {
            val seqOfDomainSeqs = fdecl.get.argSorts.map (sort => sortInterpretations(sort).toIndexedSeq).toIndexedSeq
            val argumentLists = new CartesianSeqProduct[Value](seqOfDomainSeqs)
            val inverseSortMappings: Map[Value, Z3Expr] = sortMappings.map(_.swap)
            var argumentMapping: ListMap[Seq[Value], Value] = ListMap.empty
            argumentLists.foreach (args => {
                val returnExpr = model.evaluate(z3Decl.apply(args.map(a => inverseSortMappings(a)):_*), true)
                var v: Value = Term.mkTop
                if (z3Decl.getRange.isInstanceOf[Z3BoolSort])
                    v = if (returnExpr.isTrue) Term.mkTop else Term.mkBottom
                else if (z3Decl.getRange.isInstanceOf[Z3IntSort])
                    v = IntegerLiteral(returnExpr.toString.toInt)
                else
                    v = sortMappings(returnExpr)
                argumentMapping += (args -> v)
            })
            argumentMapping
        }
    ).toMap
}
