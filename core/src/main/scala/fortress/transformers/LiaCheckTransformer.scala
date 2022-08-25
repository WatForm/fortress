package fortress.transformers
import fortress.msfol._

class LiaCheckTransformer extends ProblemStateTransformer {

    def isLia(term:Term): Boolean = checkTerm(term)._1

    def checkTerm(term: Term): (Boolean, Boolean) = term match {
        case BuiltinApp(IntPlus, Seq(t1, t2)) => (isLia(t1)&isLia(t2), false)
        case BuiltinApp(IntSub, Seq(t1, t2)) => (isLia(t1)&isLia(t2), false)
        case BuiltinApp(IntMult, Seq(t1, t2)) => {
            val (isLia1, hasVar1) = checkTerm(t1)
            val (isLia2, hasVar2) = checkTerm(t2)
            (isLia1|isLia2|(!(hasVar1&hasVar2)), hasVar1|hasVar2)
        }
        case Var(_) => (true, true)
        case AndList(args) => {
            var _isLia: Boolean = true
            for(arg <- args) {
                val (l, r) = checkTerm(arg)
                _isLia = _isLia & l
            }
            (_isLia, false)
        }
        case Not(body) => checkTerm(body)

    }

    /** Takes in a Problem, applies some transformation to it, and produces a
      * new ProblemState. Note that this does not mutate the ProblemState object, only
      * produces a new one. */
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skolemConstants, skolemFunctions, rangeRestrictions, unapplyInterp, distinctConstants) => {

        }
    }

    override def name: String = "LinearArithmeticCheckTransformer"
}
