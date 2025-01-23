package fortress.transformers

import fortress.transformers.ProblemStateTransformer
import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.problemstate.ExactScope
import fortress.interpretation.Interpretation
import fortress.sortinference.ValuedSortSubstitution

object PermissiveOPFITransformer extends OPFITransformer {

    def handleForall(quants: Seq[AnnotatedVar], body: Term,
        down: DownInfo,
        transform: (Term, DownInfo) => (Term, Set[Term]),
        opfiSort: Sort,
    ): (Term, Set[Term]) = {
        // Separate out integer variables
        val (intQuantNames, nonintQuants) = quants partitionMap (_ match {
            case AnnotatedVar(Var(name), IntSort) =>
                Left(name)
            case AnnotatedVar(variable, sort) =>
                Right(AnnotatedVar(variable, sort))
        })
        // Integer variables become opfi variables
        val intQuants = intQuantNames map (name => AnnotatedVar(Var(name), opfiSort))
        // The non-integer variables remain the same
        val newQuants = intQuants ++ nonintQuants
        val newDown = down.quantified(intQuantNames.toSet, nonintQuants.map(_.name).toSet)
        
        val (transformedBody, bodyUnknown) = transform(body, newDown)

        // Unknown if every value is unknown (This is permissive)
        val upTerms: Set[Term] = Set(Forall(newQuants, unknown(bodyUnknown)))

        // If the body is unknown, ignore it by making it true
        val newBody = knownOrTrue(transformedBody, bodyUnknown)

        polaritySimplify(Forall(newQuants, newBody), upTerms, down)
    }

    def handleExists(quants: Seq[AnnotatedVar], body: Term,
        down: DownInfo,
        transform: (Term, DownInfo) => (Term, Set[Term]),
        opfiSort: Sort,
    ): (Term, Set[Term]) = {
        // Separate out integer variables
        val (intQuantNames, nonintQuants) = quants partitionMap (_ match {
            case AnnotatedVar(Var(name), IntSort) =>
                Left(name)
            case AnnotatedVar(variable, sort) =>
                Right(AnnotatedVar(variable, sort))
        })
        // Integer variables become opfi variables
        val intQuants = intQuantNames map (name => AnnotatedVar(Var(name),opfiSort))
        // The non-integer variables remain the same
        val newQuants = intQuants ++ nonintQuants
        val newDown = down.quantified(intQuantNames.toSet, nonintQuants.map(_.name).toSet)
        
        val (transformedBody, bodyUnknown) = transform(body, newDown)

        // Unknown if every value is unknown (This is permissive)
        val upTerms: Set[Term] = Set(Forall(newQuants, unknown(bodyUnknown)))

        // If the body is unknown, ignore it by making it false
        val newBody = knownOrFalse(transformedBody, bodyUnknown)

        polaritySimplify(Exists(newQuants, newBody), upTerms, down)
    }
}
