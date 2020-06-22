package fortress.interpretation

import fortress.msfol._
import fortress.solverinterface._
import fortress.data.CartesianSeqProduct

import scala.collection.immutable.ListMap

import com.microsoft.z3.{
    Model => Z3Model,
	Context => Z3Context,
    BoolSort => Z3BoolSort,
	IntSort => Z3IntSort,
	Expr => Z3Expr
}

class Z3ApiInterpretation(model: Z3Model, sig: Signature, converter: TheoryToZ3_StringParse) extends Interpretation {

    // Map from Z3's domain elements to our domain elements
    val sortMappings: Map[Z3Expr, DomainElement] = (
        // Iterate over the the Z3 constants, determining which of them are the constants
        // we use to simulate domain elements
        // Map the Z3 value of such a constant to the Fortress domain element that the constant simulates
        for {
            z3Decl <- model.getConstDecls
            constantName = z3Decl.getName.toString if constantName.charAt(0) == '@'
        } yield {
            val sortName = z3Decl.getRange.getName.toString
            model.getConstInterp(z3Decl) -> DomainElement(constantName.substring(1,constantName.length-sortName.length).toInt, SortConst(sortName))
        }
    ).toMap

    val constantInterpretations: Map[AnnotatedVar, Value] = (
        // Iterate over the constants that do not simulate domain elements
		for {
			(constName, z3Decl) <- converter.constantConversionsMap
			v = sig.queryConstant(Var(constName))
			expr = model.evaluate(z3Decl.apply(), true) if v.isDefined
		} yield v.get -> {
			v.get.sort match {
				case BoolSort => if (expr.isTrue) Top else Bottom
				case IntSort => IntegerLiteral(expr.toString.toInt)
				case _ => sortMappings(expr)
			}
		}
	).toMap

    val sortInterpretations: Map[Sort, Seq[Value]] = (
        for {
            z3Sort <- model.getSorts
            t = Sort.mkSortConst(z3Sort.getName.toString) if sig.hasSort(t)
        } yield t -> ((1 to model.getSortUniverse(z3Sort).length) map { DomainElement(_,t) })
    ).toMap + (Sort.Bool -> Seq(Top, Bottom))

    val functionInterpretations: Map[fortress.msfol.FuncDecl, ListMap[Seq[Value], Value]] = (
			for {
				(functionName, z3Decl) <- converter.functionConversionsMap
				fdecl = sig.queryUninterpretedFunction(functionName) if fdecl.isDefined
			} yield fdecl.get -> {
				val seqOfDomainSeqs = fdecl.get.argSorts.map (sort => sortInterpretations(sort).toIndexedSeq).toIndexedSeq
				val argumentLists = new CartesianSeqProduct[Value](seqOfDomainSeqs)
				var inverseSortMappings: Map[Value, Z3Expr] = sortMappings.map(_.swap)
				inverseSortMappings = inverseSortMappings + (Top -> converter.context.mkTrue) + (Bottom -> converter.context.mkFalse)
				var argumentMapping: ListMap[Seq[Value], Value] = ListMap.empty
				argumentLists.foreach (args => {
					val returnExpr = model.evaluate(z3Decl.apply(args.map(a => inverseSortMappings(a)):_*), true)
					var v: Value = Top
					if (z3Decl.getRange.isInstanceOf[Z3BoolSort])
						v = if (returnExpr.isTrue) Top else Bottom
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
