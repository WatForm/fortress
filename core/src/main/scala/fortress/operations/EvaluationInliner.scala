package fortress.operations

import fortress.msfol._

class EvaluationInliner(theory: Theory) extends NaturalEachTermRecursion {

    private val evaluator = new Evaluator(theory)

    override def mapTerm(term: Term): Term =
        if (term.isInstanceOf[Value] || children(term).forall(_.isInstanceOf[Value]))
            evaluator.evaluate(term).getOrElse(term)
        else term

    private def children(term: Term): Seq[Term] = term match {
        case leaf: LeafTerm => Seq()
        case Not(p) => Seq(p)
        case AndList(args) => args
        case OrList(args) => args
        case Distinct(args) => args
        case Implication(left, right) => Seq(left, right)
        case Iff(left, right) => Seq(left, right)
        case Eq(left, right) => Seq(left, right)
        case App(_, args) => args
        case BuiltinApp(_, args) => args
        case Closure(_, arg1, arg2, fixedArgs) => Seq(arg1, arg2) ++ fixedArgs
        case ReflexiveClosure(_, arg1, arg2, fixedArgs) => Seq(arg1, arg2) ++ fixedArgs
        case Exists(_, body) => Seq(body)
        case Forall(_, body) => Seq(body)
        case IfThenElse(cond, t, f) => Seq(cond, t, f)
    }

}
