package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._

class SymmetryBreakingTransformerTWO(scopes: Map[Sort, Int]) extends TheoryTransformer {
        
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
        def numUnusedDomainElements(sort: Sort): Int = scopes(sort) - usedDomainElements(sort).size
        
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
        
        // Functions first
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then largest # of unused result values
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else (numUnusedDomainElements(f1.resultSort)
                > numUnusedDomainElements(f2.resultSort))
        } 
        
        val functions = theory.functionDeclarations.filter(! _.resultSort.isBuiltin)
        
        for(f <- functions) {
            val resultSort = f.resultSort
            val scope = scopes(resultSort)
            val usedVals = usedDomainElements(resultSort).toIndexedSeq
            
            if(stillUnusedDomainElements(resultSort)) {
                if (f.isDomainRangeDistinct) {
                    // DRD scheme
                    val fEqualities = Symmetry.drdFunctionEqualities(f, scopes, usedVals)
                    
                    // Add to constraints
                    constraints ++= fEqualities
                    // Add to used values
                    markUsed(fEqualities flatMap (_.domainElements))
                    
                } else {
                    // Extended CS scheme
                    val fEqualities = Symmetry.csFunctionExtEqualities(f, scope, usedVals)
                    
                    // Add to constraints
                    constraints ++= fEqualities
                    // Add to used values
                    markUsed(fEqualities flatMap (_.domainElements))
                }
            }
        }
         
        // Predicates next
        def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
            // Lowest arity
            P1.arity < P2.arity
        }
        
        val predicates = theory.functionDeclarations.filter(_.resultSort == BoolSort)
        
        for(P <- predicates) {
            if(P.argSorts forall stillUnusedDomainElements) {
                val usedValues: Map[Sort, IndexedSeq[DomainElement]] = usedDomainElements map {
                    case (sort, setOfVals) => (sort, setOfVals.toIndexedSeq)
                }
                val pImplications = Symmetry.predicateImplications(P, scopes, usedValues)
                
                // Add to constraints
                constraints ++= pImplications
                // Add to used values
                markUsed(pImplications flatMap (_.domainElements))
            }
        }
        
        theory.withAxioms(constraints.toList)
    }
    
    val name: String = "Symmetry Breaking Transformer - TWO" 
}
