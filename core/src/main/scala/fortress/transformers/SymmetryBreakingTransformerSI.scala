package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

// TODO: move this into a symmetry breaker

/**
  * Do sort inference, generate symmetry breaking constraints, then map those
  * constraints back to the original sorts.
  * For testing purposes we wanted to eliminate the question of how the solver
  * performs when given different numbers of sorts (since we just wanted to
  * test its impact on symmetry breaking).
  */
class SymmetryBreakingTransformerSI(
    selectionHeuristic: SelectionHeuristic,
    symmetryBreakerFactory: SymmetryBreakerFactory
) extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            // Perform sort inference first
            val (infTheory, substitution) = theory.inferSorts
            val infScopes = {
                for { sort <- infTheory.sorts if !sort.isBuiltin }
                yield {sort -> scopes(substitution(sort))}
            }.toMap

            // If sort substitution is identity, perform symmetry breaking as normal
            if(substitution.isIdentity) return (new SymmetryBreakingTransformer(selectionHeuristic, symmetryBreakerFactory)).apply(problemState)

            // Perform symmetry breaking on inferred theory, but select as if it wasn't there
            val breaker = symmetryBreakerFactory.create(infTheory, infScopes)
            val selector = new SelectAfterSubstitution(selectionHeuristic, substitution)

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
                selector.nextFunctionPredicate(breaker.stalenessState, remaining) match {
                    case None => ()
                    case Some(p_sub @ FuncDecl(_, _, BoolSort)) => {
                        // Have to look up function by name since sorts are substituted
                        val p = infTheory.signature.functionWithName(p_sub.name).get
                        breaker.breakPredicate(p)
                        loop(usedFunctionsPredicates + p)
                    }
                    case Some(f_sub) => {
                        // Have to look up function by name since sorts are substituted
                        val f = infTheory.signature.functionWithName(f_sub.name).get
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

            // Add symmetry breaking function declarations, constraints, and range restrictions
            val newTheory = theory.withFunctionDeclarations(newDecls).withAxioms(newConstraints)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions, unapplyInterp, distinctConstants)
        }
    }
    
    val name: String = s"Symmetry Breaking Transformer SI (${selectionHeuristic.name})" 
}
