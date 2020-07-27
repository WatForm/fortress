package fortress.interpretation

import fortress.msfol._
import fortress.solverinterface._
import fortress.data.CartesianSeqProduct
import fortress.util.Errors

import scala.collection.immutable.ListMap

import com.microsoft.z3.{
    Model => Z3Model,
	Context => Z3Context,
    BoolSort => Z3BoolSort,
	IntSort => Z3IntSort,
	Expr => Z3Expr
}

class Z3ApiInterpretation(
    model: Z3Model,
    sig: Signature,
    converter: TheoryToZ3_StringParse
) extends EvaluationBasedInterpretation(sig) {
    
    // Map from Z3's domain elements to our domain elements
    lazy val sortMappings: Map[Z3Expr, DomainElement] = (
        // Iterate over the the Z3 constants, determining which of them are the constants
        // we use to simulate domain elements
        // Map the Z3 value of such a constant to the Fortress domain element that the constant simulates
        for {
            z3Decl <- model.getConstDecls
            constantName = z3Decl.getName.toString
            domainElement <- DomainElement.interpretName(constantName)
        } yield (model.getConstInterp(z3Decl) -> domainElement)
    ).toMap
    
    override def evaluateConstant(c: AnnotatedVar): Value = {
        val z3Decl = converter.constantConversionsMap(c.name)
        val z3Sort = converter.sortConversions(c.sort)
        val expr = model.evaluate(z3Decl.apply(), true)
        c.sort match {
            case BoolSort => if (expr.isTrue) Top else Bottom
            case IntSort => IntegerLiteral(expr.toString.toInt)
            case _ => sortMappings(expr)
        }
    }
    
    override def evaluateSort(s: Sort): Seq[Value] = {
        val z3Sort = converter.sortConversions(s)
        DomainElement.range(1 to model.getSortUniverse(z3Sort).length, s)
    }
    
    override def evaluateFunction(f: FuncDecl, argList: Seq[Value]): Value = {
        
        val z3Decl = converter.functionConversionsMap(f.name)
        
        var inverseSortMappings: Map[Value, Z3Expr] = sortMappings.map(_.swap)
        inverseSortMappings += (Top -> converter.context.mkTrue)
        inverseSortMappings += (Bottom -> converter.context.mkFalse)
        
        val argListZ3 = argList map inverseSortMappings
        val returnExpr = model.evaluate(
            z3Decl.apply(argListZ3 : _*),
            true
        )
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
