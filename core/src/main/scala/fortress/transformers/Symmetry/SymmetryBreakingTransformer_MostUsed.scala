// NAD 2024-07-07 perhaps this file can be removed?

package fortress.transformers

import fortress.msfol._
import fortress.symmetry._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
  * to have domain elements in its formulas. The output formula will have domain
  * elements in its formulas. The resulting Problem has the same scopes, contains
  * the original axioms plus additional symmetry breaking axioms, and is
  * equisatisfiable to the original.
  */
class SymmetryBreakingTransformer_MostUsed(
                                            selectionHeuristicFactory: SelectionHeuristicWithConstantsFactory,
                                            symmetryBreakerFactory: SymmetryBreakerFactoryDL
                                          ) extends ProblemStateTransformer {

    def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        
        // This weirdness exists to make sure that this version performs symmetry breaking
        // on functions in the same order as the previous version
        // It is only here for the sake of consistency
        val functions = theory.functionDeclarations filter { fn => {
            (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
        }
        }
        val predicates = theory.functionDeclarations.filter { fn => {
            (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
        }
        }

        val fp = scala.collection.immutable.ListSet((functions.toList ++ predicates.toList): _*)
        // END OF WEIRDNESS

        val stalnessTracker = StalenessTracker.create(theory, scopes)
        val remainingTracker = RemainingIdentifiersTracker.create(theory.constantDeclarations, fp)

        val breaker = symmetryBreakerFactory.create(theory, scopes, stalnessTracker, remainingTracker)
        val selectionHeuristic = selectionHeuristicFactory.create(stalnessTracker, remainingTracker)

        // Set up the selection heuristic if it is using a preplanned order
        if (selectionHeuristic.isPreplannedOrder) selectionHeuristic match {
            case lowArityFirstAndMostUsedOrder: LowArityFirstAndMostUsedOrder =>
                lowArityFirstAndMostUsedOrder.preprocess(theory.mostUsedDeclarations)
            case lowArityFirstMostUsedFunctionFirstOrder: LowArityFirstMostUsedFunctionFirstOrder =>
                lowArityFirstMostUsedFunctionFirstOrder.preprocess(theory.mostUsedDeclarations)
            case _ =>
        }

        @scala.annotation.tailrec
        def loop(): Unit = {
            selectionHeuristic.nextSelection() match {
                case None => ()
                case Some(Left(constants: Seq[AnnotatedVar])) =>
                    breaker.breakListOfConstants(constants.toIndexedSeq)
                    loop()
                case Some(Right(p@FuncDecl(_, _, BoolSort))) =>
                    breaker.breakPredicate(p)
                    loop()
                case Some(Right(f@FuncDecl(_, _, _))) =>
                    breaker.breakFunction(f)
                    loop()
            }
        }

        loop()

        val newTheory = theory.withFunctionDeclarations(breaker.declarations).withAxioms(breaker.constraints)

        // ProblemState(newTheory, scopes, skc, skf, rangeRestricts union breaker.rangeRestrictions.toSet, unapplyInterp, distinctConstants)
        problemState.copy(
            theory = newTheory,
            rangeRestrictions = problemState.rangeRestrictions union breaker.rangeRestrictions.toSet,
        )
    }
    /*
    val name: String = s"Symmetry Breaking Transformer Most Used (${selectionHeuristicFactory.name})"
    */
}
