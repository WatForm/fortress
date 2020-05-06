package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.data.CartesianSeqProduct

import scala.collection.immutable.Seq

import scala.math.min

/** Introduces (quantifier-free) range formulas restricting the ranges of
  * function applications and constants.
  * This transformation is parameterized by scopes mapping sorts to sizes.
  * Note: performs no symmetry breaking.
  */
class RangeFormulaTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Sort, Integer]) = this({
        val scopes1: Map[Sort, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = {
        // Builtin types have no scopes
        Errors.precondition(scopes.forall { case (sort, size) => ! sort.isBuiltin })
        // All scoped typed are within the theory
        Errors.precondition(scopes.keySet subsetOf theory.sorts)
        // Each scope is strictly positive
        Errors.precondition(scopes.values.forall(_ > 0))
        
        // Generate range constraints for constants
        val constantRangeConstraints = for(c <- theory.constants if !c.sort.isBuiltin) yield {
            val possibleEqualities = 
                for(i <- 1 to scopes(c.sort)) yield
                    { c.variable === DomainElement(i, c.sort) }
            val rangeFormula = OrList(possibleEqualities)
            rangeFormula
        }
        
        // Generate range constraints for functions
        val functionRangeConstraints = new scala.collection.mutable.ListBuffer[Term]()
        for(f <- theory.functionDeclarations if !f.resultSort.isBuiltin) {
            val possibleRangeValues = for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)
            
            //  f: A_1 x ... x A_n -> B
            // and each A_i has generated domain D_i
            // get the list [D_1, ..., D_n]
            // If some A_i is builtin, instead make a variable x_i and quantify 
            // over it, and make the list D_i = (x_i)
            val quantifiedVarsBuffer = new scala.collection.mutable.ListBuffer[AnnotatedVar]()
            var counter = 0
            val seqOfDomainSeqs: IndexedSeq[IndexedSeq[Term]] = f.argSorts.toIndexedSeq.map (sort => {
                val Di: IndexedSeq[Term] = if (sort.isBuiltin) {
                    val annotatedVar = Var("@x_" + counter.toString) of sort
                    counter += 1
                    quantifiedVarsBuffer += annotatedVar
                    IndexedSeq(annotatedVar.variable)
                } else {
                    for(j <- 1 to scopes(sort)) yield DomainElement(j, sort)
                }
                Di
            })
            val quantifiedVars = quantifiedVarsBuffer.toList
            
            // Take the product D_1 x ... x D_n
            val argumentLists: Iterable[Seq[Term]] = new CartesianSeqProduct[Term](seqOfDomainSeqs)
            // For each tuple of arguments, add a range constraint
            argumentLists.foreach ( argumentList => {
                val possibleEqualities = for(rangeValue <- possibleRangeValues) yield {
                    App(f.name, argumentList) === rangeValue
                }
                if(quantifiedVarsBuffer.nonEmpty) {
                    functionRangeConstraints += Forall(quantifiedVars, OrList(possibleEqualities))
                } else {
                    functionRangeConstraints += OrList(possibleEqualities)
                }
            })
        }
        
        theory.withAxioms(constantRangeConstraints).withAxioms(functionRangeConstraints.toList)
    }
    
    override def name: String = "Range Formula Transformer (No Sym Break)"
}
