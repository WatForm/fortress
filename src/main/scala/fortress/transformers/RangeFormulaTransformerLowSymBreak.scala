package fortress.transformers

import scala.collection.JavaConverters._

import fortress.tfol._
import fortress.util.Errors
import fortress.data.CartesianProduct

import scala.math.min

/** Introduces (quantifier-free) range formulas restricting the ranges of
  * function applications and constants.
  * This transformation is parameterized by scopes mapping types to sizes.
  * Performs a low amount of symmetry breaking.
  * The input theory must be quantifier-free.
  * It is required that domain elements must be permutable within the input theory
  * (for example, if a the theory was the result of instantiating a theory that had
  * no explicit domain elements).
  * Only new constaints are added; no other aspect of the theory is changed.
  */
class RangeFormulaTransformerLowSymBreak(scopes: Map[Type, Int]) extends TheoryTransformer {
    // Ugly conversion from Java data structures
    def this(scopes: java.util.Map[Type, Integer]) = this({
        val scopes1: Map[Type, Integer] = scopes.asScala.toMap
        scopes1.map { case (sort, size: Integer) => (sort, Predef.Integer2int(size)) }
    })
    
    override def apply(theory: Theory): Theory = {
        Errors.precondition(!scopes.contains(Type.Bool))
        Errors.precondition(scopes.keySet subsetOf theory.types)
        Errors.precondition(scopes.values.forall(_ > 0))
        
        val maximalDesignatedNumber = scala.collection.mutable.Map[Type, Int]()
        scopes.foreach { case (sort, size) => maximalDesignatedNumber += (sort -> 0) }
        
        // Generate range constraints for constants
        val constantRangeConstraints = for(c <- theory.constants if c.sort != Type.Bool) yield {
            val possibleEqualities = 
                for(i <- 1 to min(scopes(c.sort), maximalDesignatedNumber(c.sort) + 1)) yield
                    { c.variable === DomainElement(i, c.sort) }
            // Update maximalDesignatedNumber
            maximalDesignatedNumber(c.sort) = min(scopes(c.sort), maximalDesignatedNumber(c.sort) + 1)
            val rangeFormula = Or(possibleEqualities)
            rangeFormula
        }
        
        // Generate range constraints for functions
        val functionRangeConstraints = new scala.collection.mutable.ListBuffer[Term]()
        for(f <- theory.functionDeclarations if f.resultType != Type.Bool) {
            val possibleRangeValues = for(i <- 1 to scopes(f.resultType)) yield DomainElement(i, f.resultType)
            // if f: A_1 x ... x A_n -> B
            // and each A_i has generated domain D_i
            // get the list [D_1, ..., D_n]
            val seqOfDomainSeqs: Seq[Seq[Term]] = f.argTypes.map (sort => 
                for(i <- 1 to scopes(sort)) yield DomainElement(i, sort))
            // Take the product D_1 x ... x D_n
            val seqOfDomainSeqsJava = seqOfDomainSeqs.map(domainSeq => domainSeq.asJava).asJava
            val argumentLists: java.lang.Iterable[java.util.List[Term]] = new CartesianProduct[Term](seqOfDomainSeqsJava)
            // For each tuple of arguments, add a range constraint
            argumentLists.forEach ( argumentList => {
                val possibleEqualities = for(rangeValue <- possibleRangeValues) yield {
                    Term.mkApp(f.name, argumentList) === rangeValue
                }
                functionRangeConstraints += Or(possibleEqualities)
            })
        }
        
        theory.withAxioms(constantRangeConstraints).withAxioms(functionRangeConstraints.toList)
    }
    
    override def getName: String = "Range Formula Transformer (Low Sym Break)"
}