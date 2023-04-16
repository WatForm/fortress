import org.scalatest._
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.problemstate.ExactScope
import fortress.symmetry._

class SelectionHeuristicWithConstantsTests extends UnitSuite with CommonSymbols {
    val x1_const: AnnotatedVar = x1 of A
    val x2_const: AnnotatedVar = x2 of A
    val x3_const: AnnotatedVar = x3 of B
    val x4_const: AnnotatedVar = x4 of C

    val f_func: FuncDecl = f from A to A
    val P_func: FuncDecl = P from B to C
    val Q_func: FuncDecl = Q from(A, A) to A
    val R_pred: FuncDecl = R from A to BoolSort
    val S_pred: FuncDecl = S from(C, A) to BoolSort
    val T_pred: FuncDecl = T from B to BoolSort

    test("Low Arity First And Most Used Order") {
        val factory = LowArityFirstAndMostUsedOrderFactory

        val theory = Theory.empty
          .withSorts(A, B, C)
          .withConstantDeclarations(x1_const, x2_const, x3_const, x4_const)
          .withFunctionDeclarations(f_func, P_func, Q_func, R_pred, S_pred, T_pred)

        val stalnessTracker = StalenessTracker.create(theory, Map(A -> ExactScope(2), B -> ExactScope(3), C -> ExactScope(3)))
        val remainingTracker = RemainingIdentifiersTracker.create(theory.constantDeclarations, theory.functionDeclarations)

        val selectionHeuristic = factory.create(stalnessTracker, remainingTracker)

        // If we didn't do preprocess work, then the selection heuristic selects nothing
        selectionHeuristic.nextSelection() should be(None)

        // Set up the selection heuristic if it is using a preplanned order
        if (selectionHeuristic.isPreplannedOrder) selectionHeuristic match {
            case lowArityFirstAndMostUsedOrder: LowArityFirstAndMostUsedOrder =>
                lowArityFirstAndMostUsedOrder.preprocess(Map(
                    x1_const -> 1,
                    x2_const -> 2,
                    x3_const -> 3,
                    x4_const -> 4,
                    f_func -> 1,
                    P_func -> 2,
                    Q_func -> 5,
                    R_pred -> 3,
                    S_pred -> 4,
                    T_pred -> 2))
            case _ =>
        }

        var list: List[Declaration] = List.empty

        @scala.annotation.tailrec
        def loop(): Unit = {
            selectionHeuristic.nextSelection() match {
                case None => ()
                case Some(Left(constants: Seq[AnnotatedVar])) =>
                    list = list ++ constants
                    loop()
                case Some(Right(p@FuncDecl(_, _, BoolSort))) =>
                    list = list :+ p
                    loop()
                case Some(Right(f@FuncDecl(_, _, _))) =>
                    list = list :+ f
                    loop()
            }
        }

        loop()

        // Constants first: x4, x3, x2, x1
        // then arity one functions/predicates: R_pred, T_pred, P_func, f_func
        // then arity two functions/predicates: Q_func, S_pred
        val expectedList = List(x4_const, x3_const, x2_const, x1_const, R_pred, T_pred, P_func, f_func, Q_func, S_pred)

        list should equal(expectedList)
    }
}
