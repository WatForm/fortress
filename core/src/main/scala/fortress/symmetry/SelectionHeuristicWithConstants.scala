package fortress.symmetry

import fortress.msfol._
import fortress.util.Errors


trait SelectionHeuristicWithConstantsFactory {
    def create(stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker): SelectionHeuristicWithConstants

    def name: String
}

abstract class SelectionHeuristicWithConstants(stalenessTrackerParam: StalenessTracker, remainingTrackerParam: RemainingIdentifiersTracker) {

    protected val stalenessTracker: StalenessTracker = stalenessTrackerParam
    protected val remainingTracker: RemainingIdentifiersTracker = remainingTrackerParam

    def name: String

    // Whether it is done in a preplanned order
    def isPreplannedOrder: Boolean

    // Select the next sequence of constants, or one function/predicate
    def nextSelection(): Option[Either[Seq[AnnotatedVar], FuncDecl]]
}

class LowArityFirstAndMostUsedOrder(stalenessTrackerParam: StalenessTracker, remainingTrackerParam: RemainingIdentifiersTracker)
  extends SelectionHeuristicWithConstants(stalenessTrackerParam: StalenessTracker, remainingTrackerParam: RemainingIdentifiersTracker) {

    override def name = "Low Arity First, Then Most Used"

    override def isPreplannedOrder: Boolean = true

    var preplannedOrder: Seq[Declaration] = Seq.empty

    // We need profiling info to determine the preplanned order
    def preprocess(profilingInfo: Map[Declaration, Int]): Unit = {
        // Comparison operation for constants to determine which order to
        // perform symmetry breaking
        def consLessThan(c1: AnnotatedVar, c2: AnnotatedVar): Boolean = {
            // Most used first
            Errors.Internal.precondition(profilingInfo.contains(c1) && profilingInfo.contains(c2),
                "Constants " + c1.name + " or " + c1.name + " cannot be found in the profiling info")
            profilingInfo(c1) > profilingInfo(c2)
        }

        // Comparison operation for functions/predicates to determine which order
        // to perform symmetry breaking
        def fnLessThan(f1: FuncDecl, f2: FuncDecl): Boolean = {
            // Lowest arity, then most used
            if (f1.arity < f2.arity) true
            else if (f1.arity > f2.arity) false
            else {
                Errors.Internal.precondition(profilingInfo.contains(f1) && profilingInfo.contains(f2),
                    "Function declarations " + f1.name + " or " + f2.name + " cannot be found in the profiling info")
                profilingInfo(f1) > profilingInfo(f2)
            }
        }

        preplannedOrder = (remainingTracker.remainingConstants.toSeq sortWith consLessThan) ++
          (remainingTracker.remainingFuncDecls.toSeq sortWith fnLessThan)
    }

    override def nextSelection(): Option[Either[Seq[AnnotatedVar], FuncDecl]] = {
        if (preplannedOrder.nonEmpty) {
            preplannedOrder.head match {
                case decl: FuncDecl =>
                    // Return the first function or predicate
                    preplannedOrder = preplannedOrder.drop(1)
                    return Some(Right(decl))
                case _: AnnotatedVar =>
                    // Return the longest sequence of constants at the beginning of the preplanned order
                    val listOfConstants = preplannedOrder.takeWhile(_.isInstanceOf[AnnotatedVar]).toSeq
                    preplannedOrder = preplannedOrder.drop(listOfConstants.size)
                    return Some(Left(listOfConstants.map(_.asInstanceOf[AnnotatedVar])))
            }
        }
        None
    }
}

object LowArityFirstAndMostUsedOrderFactory extends SelectionHeuristicWithConstantsFactory {
    override def name = "Low Arity First, Then Most Used"

    def create(stalenessTracker: StalenessTracker, remainingTracker: RemainingIdentifiersTracker): SelectionHeuristicWithConstants = new LowArityFirstAndMostUsedOrder(stalenessTracker, remainingTracker)
}
