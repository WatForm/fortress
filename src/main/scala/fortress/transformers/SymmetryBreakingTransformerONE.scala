package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._

class SymmetryBreakingTransformerONE(scopes: Map[Sort, Int]) extends TheoryTransformer {
        
    def apply(theory: Theory): Theory = {
        
        // Note this an immutable map of mutable sets
        val usedDomainElements: Map[Sort, mutable.Set[DomainElement]] = {
            val allUsedDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
            val mapTuples = for (sort <- theory.sorts) yield {
                val set = allUsedDomainElements filter (_.sort == sort)
                val mutableSet = mutable.Set(set.toSeq: _*) // Annoying conversion
                (sort, mutableSet)
            }
            mapTuples.toMap
        }
        
        def markUsed(domainElements: Iterable[DomainElement]): Unit = {
            for(de <- domainElements) {
                usedDomainElements(de.sort) += de
            }
        }
        
        def stillUnusedDomainElements(sort: Sort): Boolean = usedDomainElements(sort).size < scopes(sort)
        
        val constraints = new mutable.ListBuffer[Term]
        
        // Symmetry break on constants first
        for(sort <- theory.sorts if !sort.isBuiltin) {
            val constants = theory.constants.filter(_.sort == sort).toIndexedSeq
            val usedVals = usedDomainElements(sort).toIndexedSeq
            val scope = scopes(sort)
            val constantEqualities = Symmetry.csConstantEqualities(sort, constants, scope, usedVals)
            val constantImplications = Symmetry.csConstantImplications(sort, constants, scope, usedVals)
            
            // Add to constraints
            constraints ++= constantEqualities
            constraints ++= constantImplications
            // Add to used values
            markUsed(constantEqualities flatMap (_.domainElements))
            markUsed(constantImplications flatMap (_.domainElements))
        }
        
        // Search for functions of the form f: A x ... x A -> A
        def isAtoA(f: FuncDecl): Boolean = f.argSorts.forall(_ == f.resultSort) && !f.resultSort.isBuiltin
        
        // We don't really care what order we break these functions in
        // Even arity doesn't make a difference, since it all boils
        // down to symmetry breaking a unary function
        for(f <- theory.functionDeclarations if isAtoA(f)) {
            val sort = f.resultSort
            val scope = scopes(sort)
            val usedVals = usedDomainElements(sort).toIndexedSeq
            if(stillUnusedDomainElements(sort)) {
                val fEqualities = Symmetry.csFunctionExtEqualities(f, scope, usedVals)
                
                // Add to constraints
                constraints ++= fEqualities
                // Add to used values
                markUsed(fEqualities flatMap (_.domainElements))
            }
        }
        
        theory.withAxioms(constraints.toList)
    }
    
    val name: String = "Symmetry Breaking Transformer - ONE" 
}
