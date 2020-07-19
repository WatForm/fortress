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
            constantName = z3Decl.getName.toString
            domainElement <- DomainElement.interpretName(constantName)
        } yield (model.getConstInterp(z3Decl) -> domainElement)
    ).toMap

    val constantInterpretations: Map[AnnotatedVar, Value] = (
		for {
			(constName, z3Decl) <- converter.constantConversionsMap
            if DomainElement.interpretName(constName).isEmpty // Exclude domain constants
			v @ AnnotatedVar(variable, sort) <- sig.queryConstant(Var(constName))
		} yield v -> {
            val expr = model.evaluate(z3Decl.apply(), true)
			sort match {
				case BoolSort => if (expr.isTrue) Top else Bottom
				case IntSort => IntegerLiteral(expr.toString.toInt)
				case _ => sortMappings(expr)
			}
		}
	).toMap

    val sortInterpretations: Map[Sort, Seq[Value]] = (
        for {
            z3Sort <- model.getSorts
            s = Sort.mkSortConst(z3Sort.getName.toString)
            if sig.hasSort(s)
        } yield s -> {
            (1 to model.getSortUniverse(z3Sort).length) map { DomainElement(_, s) }
        }
    ).toMap + (Sort.Bool -> Seq(Top, Bottom))

    val functionInterpretations: Map[fortress.msfol.FuncDecl, Map[Seq[Value], Value]] = (
			for {
				(functionName, z3Decl) <- converter.functionConversionsMap
				fdecl <- sig.queryUninterpretedFunction(functionName)
			} yield fdecl -> {
				val seqOfDomainSeqs = fdecl.argSorts.map (sort => sortInterpretations(sort).toIndexedSeq).toIndexedSeq
				val argumentLists = new CartesianSeqProduct[Value](seqOfDomainSeqs)
				var inverseSortMappings: Map[Value, Z3Expr] = sortMappings.map(_.swap)
				inverseSortMappings += (Top -> converter.context.mkTrue)
                inverseSortMappings += (Bottom -> converter.context.mkFalse)
				
                val argumentMapping: Map[Seq[Value], Value] = (
                    for(argList <- argumentLists) yield {
                        val argListZ3 = argList map inverseSortMappings
                        val returnExpr = model.evaluate(
                            z3Decl.apply(argListZ3 : _*),
                            true
                        )
    					argList -> {
                            if (z3Decl.getRange.isInstanceOf[Z3BoolSort]) {
                                if (returnExpr.isTrue) Top
                                else Bottom
                            } else if (z3Decl.getRange.isInstanceOf[Z3IntSort]) {
                                IntegerLiteral(returnExpr.toString.toInt)
                            } else {
                                sortMappings(returnExpr)
                            }
                        }
                    }
                ).toMap
				argumentMapping
			}
		).toMap
}
