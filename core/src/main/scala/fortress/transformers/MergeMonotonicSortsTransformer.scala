package fortress.transformers

import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.interpretation._
import fortress.operations.TermOps.wrapTerm
import fortress.operations._
import fortress.problemstate._
import fortress.transformers._

/*
  Collapse all the monotone sorts into one sort "Mono" (this operation is safe).
 */

object MergeMonotonicSortsTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val sorts = theory.sorts
            val result = new Monotonicity(theory).check()

            val monoSorts: Set[Sort] = sorts.filter(result(_))
            val MMS: MergeMonotonicSorts = new MergeMonotonicSorts(monoSorts)

            val newSorts: Set[Sort] = sorts.filterNot(result(_)) + SortConst("MONO")
            val newFuncDecls: Set[FuncDecl] = MMS.updateFuncDecls(theory.functionDeclarations)
            val newFuncDefs: Set[FunctionDefinition] = MMS.updateFuncDefs(theory.functionDefinitions)
            val newConstants: Set[AnnotatedVar] = MMS.updateConstants(theory.constants)
            val newAxioms: Set[Term] = MMS.updateAxioms(theory.axioms)
            val newScopes: Map[Sort, Scope] = MMS.updateScopes(scopes, exactScopeForMONO = true)

            val newSkolemConstants: Set[AnnotatedVar] = MMS.updateConstants(skc)
            val newSkolemFunctions: Set[FuncDecl] = MMS.updateFuncDecls(skf)
            val newRangeRestrictions: Set[RangeRestriction] = MMS.updateRangeRestrictions(rangeRestricts)

            val unapply: Interpretation => Interpretation = ???

            val newSignature: Signature = Signature(
                newSorts,
                newFuncDecls,
                newFuncDefs,
                newConstants,
                theory.enumConstants
            )

            val newTheory: Theory = Theory(newSignature, newAxioms)

            ProblemState(
                newTheory,
                newScopes,
                newSkolemConstants,
                newSkolemFunctions,
                newRangeRestrictions,
                unapply :: unapplyInterp,
                distinctConstants
            )
        }
    }

    override val name: String = "MergeMonotonicSorts Transformer"
}
