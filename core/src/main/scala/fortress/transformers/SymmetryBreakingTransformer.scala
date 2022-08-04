package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/
class SymmetryBreakingTransformer(
    selectionHeuristic: SelectionHeuristic,
    symmetryBreakerFactory: SymmetryBreakerFactory
) extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {


            val breaker = symmetryBreakerFactory.create(theory, scopes)

            // First, perform symmetry breaking on constants
            breaker.breakConstants(theory.constants)
            
            // This weirdness exists to make sure that this version performs symmetry breaking
            // on functions in the same order as the previous version
            // It is only here for the sake of consistency
            val functions = theory.functionDeclarations filter { fn => {
                (!fn.resultSort.isBuiltin && scopes.contains(fn.resultSort)) && (fn.argSorts forall (!_.isBuiltin)) && (fn.argSorts forall scopes.contains)
            }}
            val predicates = theory.functionDeclarations.filter { fn => {
                (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin)) && (fn.argSorts forall scopes.contains)
            }}
            
            val fp = scala.collection.immutable.ListSet( (functions.toList ++ predicates.toList) : _* )
            // END OF WEIRDNESS

            // Then, perform symmetry breaking on functions and predicates
            @scala.annotation.tailrec
            def loop(usedFunctionsPredicates: Set[FuncDecl]): Unit = {
                val remaining = fp diff usedFunctionsPredicates
                selectionHeuristic.nextFunctionPredicate(breaker.stalenessState, remaining) match {
                    case None => ()
                    case Some(p @ FuncDecl(_, _, BoolSort)) => {
                        if( p.argSorts forall scopes.contains ) {
                            breaker.breakPredicate(p)
                            loop(usedFunctionsPredicates + p)
                        }
                    }
                    case Some(f) => {
                        breaker.breakFunction(f)
                        loop(usedFunctionsPredicates + f)
                    }
                }
            }
            
            loop(Set.empty)

            // Add symmetry breaking function declarations, constraints, and range restrictions
            val newTheory = theory.withFunctionDeclarations(breaker.declarations).withAxioms(breaker.constraints)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union breaker.rangeRestrictions.toSet, unapplyInterp, distinctConstants)
        }
    }
    
    val name: String = s"Symmetry Breaking Transformer (${selectionHeuristic.name})" 
}
