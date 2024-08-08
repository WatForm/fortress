package fortress.operations

import fortress.msfol._

class EvaluationInliner(theory: Theory) extends NaturalEachTermBottomUpRecursion {

    private val evaluator = new Evaluator(theory)

    // Try and evaluate each term bottom-up, evaluating shallowly to avoid extra recursion.
    // Evaluating shallowly is valid because any evaluatable terms will already have been replaced.
    override def mapTerm(term: Term): Term = evaluator.shallowEvaluate(term) match {
        case Some(value) => value
        case None => term // couldn't map it
    }

}
