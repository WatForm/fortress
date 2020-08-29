package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

// TODO: move this into a symmetry breaker

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/
class SymmetryBreakingTransformerSI(
    selectionHeuristic: SelectionHeuristic,
    symmetryBreakerFactory: SymmetryBreakerFactory
) extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {

            // Perform sort inference first
            val (infTheory, substitution) = theory.inferSorts
            val infScopes = {
                for { sort <- infTheory.sorts if !sort.isBuiltin }
                yield {sort -> scopes(substitution(sort))}
            }.toMap

            // Perform symmetry breaking on inferred theory, but select as if it wasn't there

            val breaker = symmetryBreakerFactory.create(infTheory, infScopes)
            
            breaker.breakConstants(infTheory.constants)
            
            // This weirdness exists to make sure that this version performs symmetry breaking
            // on functions in the same order as the previous version
            // It is only here for the sake of consistency
            val functions = infTheory.functionDeclarations filter { fn => {
                (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
            }}
            val predicates = infTheory.functionDeclarations.filter { fn => {
                (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
            }}
            
            val fp = scala.collection.immutable.ListSet( (functions.toList ++ predicates.toList) : _* )
            // END OF WEIRDNESS
            
            @scala.annotation.tailrec
            def loop(usedFunctionsPredicates: Set[FuncDecl]): Unit = {
                val remaining = fp diff usedFunctionsPredicates
                selectionHeuristic.nextFunctionPredicate(breaker.view, remaining) match {
                    case None => ()
                    case Some(p @ FuncDecl(_, _, BoolSort)) => {
                        breaker.breakPredicate(p)
                        loop(usedFunctionsPredicates + p)
                    }
                    case Some(f) => {
                        breaker.breakFunction(f)
                        loop(usedFunctionsPredicates + f)
                    }
                }
            }
            
            loop(Set.empty)

            // Apply substitution to go back to original theory
            val newDecls = breaker.declarations.map(substitution)
            val newConstraints = breaker.constraints.map(substitution)
            val newRangeRestrictions = breaker.rangeRestrictions.toSet.map( (rr: RangeRestriction) => substitution(rr))
            
            val newTheory = theory.withFunctionDeclarations(newDecls).withAxioms(newConstraints)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions, unapplyInterp)
        }
    }
    
    val name: String = s"Symmetry Breaking Transformer SI (${selectionHeuristic.name})" 
}
