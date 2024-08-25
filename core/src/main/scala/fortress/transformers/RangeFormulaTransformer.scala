package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.data.CartesianSeqProduct
import fortress.problemstate.ProblemState

import scala.math.min



/** Introduces range formulas, restricting the output values of constants and functions.
  * Symmetry breaking is not directly performed in this step.
  * If a term already has range restriction imposed on it (for example, from symmetry breaking),
  * generation of its range formula will be skipped (since it is redundant).
  *
  * @param useConstForDomElem if true, inserts domain elements as constants; if false, inserts domain elements directly (should be defaulted to false)
  */
private[transformers] class RangeFormulaTransformer (useConstForDomElem: Boolean) extends ProblemStateTransformer {
    
    private def DE(index: Integer, sort: Sort): Term =
        if (useConstForDomElem) DomainElement(index, sort).asSmtConstant
        else DomainElement(index, sort)
    
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        val rangeRestricts = problemState.rangeRestrictions
        
        // Generate range constraints for constants
        val constantRangeConstraints = for {
            c <- theory.constantDeclarations
            if !c.sort.isBuiltin && scopes.contains(c.sort) // make sure the sort is bounded.
            // Don't generate constraints for terms that are already restricted
            if ! (rangeRestricts exists (_.term == c.variable))
        } yield {
            val possibleValues = for(i <- 1 to scopes(c.sort).size) yield DE(i, c.sort)
            val rangeFormula = c.variable equalsOneOf possibleValues
            rangeFormula
        }

        // Generate range constraints for function *declarations*
        val functionRangeConstraints = new scala.collection.mutable.ListBuffer[Term]()
        for {
            f <- theory.functionDeclarations
            if !f.resultSort.isBuiltin && scopes.contains(f.resultSort)
        } {
            val possibleRangeValues = for(i <- 1 to scopes(f.resultSort).size) yield DE(i, f.resultSort)
            
            //  f: A_1 x ... x A_n -> B
            // and each A_i has generated domain D_i
            // get the list [D_1, ..., D_n]
            // If some A_i is builtin, instead make a variable x_i and quantify 
            // over it, and make the list D_i = (x_i)
            val quantifiedVarsBuffer = new scala.collection.mutable.ListBuffer[AnnotatedVar]()
            var counter = 0
            val seqOfDomainSeqs: IndexedSeq[IndexedSeq[Term]] = f.argSorts.toIndexedSeq.map (sort => {
                val Di: IndexedSeq[Term] = if ( sort.isBuiltin || !scopes.contains(sort) ) {
                    val annotatedVar = Var("$x_" + counter.toString) of sort
                    counter += 1
                    quantifiedVarsBuffer += annotatedVar
                    IndexedSeq(annotatedVar.variable)
                } else {
                    for(j <- 1 to scopes(sort).size) yield DE(j, sort)
                }
                Di
            })
            val quantifiedVars = quantifiedVarsBuffer.toList
            
            // Take the product D_1 x ... x D_n
            val argumentLists: Iterable[Seq[Term]] = new CartesianSeqProduct[Term](seqOfDomainSeqs)
            // For each tuple of arguments, add a range constraint
            for(argumentList <- argumentLists) {
                val app = App(f.name, argumentList)
                if(quantifiedVarsBuffer.nonEmpty) {
                    functionRangeConstraints += Forall(quantifiedVars, app equalsOneOf possibleRangeValues)
                } else if (! (rangeRestricts exists (_.term == app))) { // Don't generate constraints for terms that are already restricted
                    functionRangeConstraints += app equalsOneOf possibleRangeValues
                }
            }
        }
        
        val newTheory = theory
            .withAxioms(constantRangeConstraints)
            .withAxioms(functionRangeConstraints.toList)

        problemState.withTheory(newTheory)
    }
    
    override def name: String = "Range Formula Transformer"
}

object RangeFormulaUseDEsTransformer extends RangeFormulaTransformer(false) {

}

object RangeFormulaUseConstantsTransformer extends RangeFormulaTransformer(true) {

}

