package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.data.CartesianSeqProduct
import fortress.modelfind.ProblemState

import scala.math.min

/** Introduces range formulas restricting the ranges of
  * function applications and constants.
  * The resulting problem is equisatisfiable to the original and formulaically bound.
  * Note: Symmetry breaking is not performed in this step.
  */
class RangeFormulaTransformer_NoElision private (useConstForDomElem: Boolean) extends ProblemStateTransformer {
    
    private def DE(index: Integer, sort: Sort): Term =
        if (useConstForDomElem) DomainElement(index, sort).asSmtConstant
        else DomainElement(index, sort)
    
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {
            // Generate range constraints for constants
            val constantRangeConstraints = for {
                c <- theory.constants
                if !c.sort.isBuiltin
            } yield {
                val possibleValues = for(i <- 1 to scopes(c.sort)) yield DE(i, c.sort)
                val rangeFormula = c.variable equalsOneOf possibleValues
                rangeFormula
            }
            
            // Generate range constraints for functions
            val functionRangeConstraints = new scala.collection.mutable.ListBuffer[Term]()
            for {
                f <- theory.functionDeclarations
                if !f.resultSort.isBuiltin
            } {
                val possibleRangeValues = for(i <- 1 to scopes(f.resultSort)) yield DE(i, f.resultSort)
                
                //  f: A_1 x ... x A_n -> B
                // and each A_i has generated domain D_i
                // get the list [D_1, ..., D_n]
                // If some A_i is builtin, instead make a variable x_i and quantify 
                // over it, and make the list D_i = (x_i)
                val quantifiedVarsBuffer = new scala.collection.mutable.ListBuffer[AnnotatedVar]()
                var counter = 0
                val seqOfDomainSeqs: IndexedSeq[IndexedSeq[Term]] = f.argSorts.toIndexedSeq.map (sort => {
                    val Di: IndexedSeq[Term] = if (sort.isBuiltin) {
                        val annotatedVar = Var("$x_" + counter.toString) of sort
                        counter += 1
                        quantifiedVarsBuffer += annotatedVar
                        IndexedSeq(annotatedVar.variable)
                    } else {
                        for(j <- 1 to scopes(sort)) yield DE(j, sort)
                    }
                    Di
                })
                val quantifiedVars = quantifiedVarsBuffer.toList
                
                // Take the product D_1 x ... x D_n
                val argumentLists: Iterable[Seq[Term]] = new CartesianSeqProduct[Term](seqOfDomainSeqs)
                // For each tuple of arguments, add a range constraint
                for(argumentList <- argumentLists) {
                    val app = App(f.name, argumentList)
                    if (quantifiedVarsBuffer.nonEmpty) {
                        functionRangeConstraints += Forall(quantifiedVars, app equalsOneOf possibleRangeValues)
                    } else {
                        functionRangeConstraints += app equalsOneOf possibleRangeValues
                    }
                }
            }
            
            val newTheory = theory.withAxioms(constantRangeConstraints).withAxioms(functionRangeConstraints.toList)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp)
        }
    }
    
    override def name: String = "Range Formula Transformer (No Elision)"
}

object RangeFormulaTransformer_NoElision {
    def create(): RangeFormulaTransformer_NoElision = new RangeFormulaTransformer_NoElision(false)
    def createWithDomElemsAsConstants(): RangeFormulaTransformer_NoElision = new RangeFormulaTransformer_NoElision(true)
}
