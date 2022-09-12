package fortress.operations

import fortress.msfol._

object LiaChecker {

    var varSet: Set[String] = Set.empty

    def check(term: Term): (Boolean, Set[String]) ={
        val isLia: Boolean = checkTerm(term)._1
        (isLia, varSet)
    }

    def helper(t1: Term, t2: Term): (Boolean, Boolean) = {
        val (isLia1, hasVar1) = checkTerm(t1)
        val (isLia2, hasVar2) = checkTerm(t2)
        ( isLia1&isLia2, hasVar1|hasVar2 )
    }

    def checkTerm(term: Term): (Boolean, Boolean) = term match {
        case BuiltinApp(IntPlus, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntSub, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntGE, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntGT, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntLE, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntLT, Seq(t1, t2)) => helper(t1, t2)
        case BuiltinApp(IntMult, Seq(t1, t2)) => {
            val (isLia1, hasVar1) = checkTerm(t1)
            val (isLia2, hasVar2) = checkTerm(t2)
            (isLia1&isLia2&(!(hasVar1&hasVar2)), hasVar1|hasVar2)
        }
        case BuiltinApp(IntDiv, Seq(t1, t2)) => (false, false)
        case Var(_) => {
            varSet = varSet + term.toString
            (true, true)
        }
        case App(func, args) => {
            varSet = varSet + func
            (true, true)
        }
        case AndList(args) => {
            var _isLia: Boolean = true
            var _hasVar: Boolean = false
            for(arg <- args) {
                val (l, r) = checkTerm(arg)
                _isLia = _isLia & l
                _hasVar = _hasVar | r
            }
            (_isLia, _hasVar)
        }
        case OrList(args) => {
            var _isLia: Boolean = true
            var _hasVar: Boolean = false
            for(arg <- args) {
                val (l, r) = checkTerm(arg)
                _isLia = _isLia & l
                _hasVar = _hasVar | r
            }
            (_isLia, _hasVar)
        }
        case Implication(t1, t2) => helper(t1, t2)
        case Iff(t1, t2) => helper(t1, t2)
        case Forall(vars, body) => checkTerm(body)
        case Exists(vars, body) => checkTerm(body)
        case Eq(t1, t2) => helper(t1, t2)
        case IfThenElse(condition, ifTrue, ifFalse) => {
            val (isLia1, hasVar1) = checkTerm(condition)
            val (isLia2, hasVar2) = checkTerm(ifTrue)
            val (isLia3, hasVar3) = checkTerm(ifFalse)
            ( isLia1&isLia2&isLia3, hasVar1|hasVar2|hasVar3 )
        }
        case Not(body) => checkTerm(body)
        case _ => (true, false)
    }




}
