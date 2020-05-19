package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._

class SymmetryBreakingTransformerTWO(scopes: Map[Sort, Int]) extends TheoryTransformer {
        
    def apply(theory: Theory): Theory = {
        
        // Contains all used domain elements in the theory
        // This data structure is updated over time
        // Note this an immutable map of mutable sets
        val usedDomainElements: Map[Sort, mutable.Set[DomainElement]] = {
            // Determine which domain elements have been used in the original theory
            val allUsedDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
            val mapTuples = for (sort <- theory.sorts if !sort.isBuiltin) yield {
                val set = allUsedDomainElements filter (_.sort == sort)
                val mutableSet = mutable.Set(set.toSeq: _*) // Annoying conversion
                (sort, mutableSet)
            }
            mapTuples.toMap
        }
        
        // Marks domain elements as used
        def markUsed(domainElements: Iterable[DomainElement]): Unit = {
            for(de <- domainElements) {
                usedDomainElements(de.sort) += de
            }
        }
        
        // Determines whether this sort has any unused domain elements
        def stillUnusedDomainElements(sort: Sort): Boolean = usedDomainElements(sort).size < scopes(sort)
        // Determines how many unused domain elements this sort has
        def numUnusedDomainElements(sort: Sort): Int = scopes(sort) - usedDomainElements(sort).size
        
        // Accumulates the symmetry breaking constraints
        val constraints = new mutable.ListBuffer[Term]
        
        // Symmetry break on constants first
        for(sort <- theory.sorts if !sort.isBuiltin && stillUnusedDomainElements(sort)) {
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
        
        // After constants, do all of the functions
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then largest # of unused result values
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else (numUnusedDomainElements(f1.resultSort)
                > numUnusedDomainElements(f2.resultSort))
        }
        
        // Only perform symmetry breaking on functions that don't consume or produce
        // builtin types (this also filters out predicates)
        val functions = theory.functionDeclarations filter { fn => {
            (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
        }}
        
        // Apply symmetry breaking to the functions
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
         
        // After functions, do the predicates
        
        // Comparison operation for functions to determine which order
        // to perform symmetry breaking
        def predLessThan(P1: FuncDecl, P2: FuncDecl): Boolean = {
            // Lowest arity
            P1.arity < P2.arity
        }
        
        // Filter function declarations to take only the predicates
        // Additionally, do not take predicates that operate on builtin sorts 
        val predicates = theory.functionDeclarations.filter { fn => {
            (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
        }}
        
        // Apply symmetry breaking to the predicates
        for(P <- predicates) {
            if(P.argSorts forall (numUnusedDomainElements(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
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
