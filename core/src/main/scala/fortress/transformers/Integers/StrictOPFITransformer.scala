package fortress.transformers

import fortress.transformers.ProblemStateTransformer
import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.problemstate.ExactScope
import fortress.interpretation.Interpretation
import fortress.sortinference.ValuedSortSubstitution

// From permissive OPFI
import Polarity._
import _root_.fortress.msfol.OrList

object StrictOPFITransformer extends OPFITransformer {

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
        // Add the quantified variables to the context
        val newDown = down.quantified(intQuantNames.toSet, nonintQuants.map(_.name).toSet)
        
        // Transform the body recursively
        val (transformedBody, bodyUnknownTerms) = transform(body, newDown)
        val bodyIsUnknown = Or.smart(bodyUnknownTerms.toSeq)
        
        // If the body is unknown, ignore it by making it true
        val newBody = Forall(newQuants, transformedBody)

        // If there is an assignment that is unknown
        // AND no known false assignment, the value is unknown
        // STRICT
        val isUnknown: Term = AndList(
            Exists(newQuants, bodyIsUnknown),
            Not(Exists(newQuants, And(Not(transformedBody), Not(bodyIsUnknown))))
        )

        polaritySimplify(newBody, Set(isUnknown), down)
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
        val intQuants = intQuantNames map (name => AnnotatedVar(Var(name), opfiSort))
        // The non-integer variables remain the same
        val newQuants = intQuants ++ nonintQuants
        // Add the quantified variables to the context
        val newDown = down.quantified(intQuantNames.toSet, nonintQuants.map(_.name).toSet)
        
        // Transform the body recursively
        val (transformedBody, bodyUnknownTerms) = transform(body, newDown)
        val bodyIsUnknown = Or.smart(bodyUnknownTerms.toSeq)
        
        // We don't need to neutralize the body
        // Either the entire term overflows, or there is a valid true
        // In either case, this value is irrelevant.
        // Result is invalid if any substitutions are invalid
        // and no valid substitution is true.
        // Essentially the same as disjunction
        val newBody = Exists(newQuants, transformedBody)

        // If there is an assignment that is unknown
        // AND no known false assignment, the value is unknown
        // STRICT
        val isUnknown: Term = AndList(
            Exists(newQuants, bodyIsUnknown),
            Not(Exists(newQuants, And(transformedBody, Not(bodyIsUnknown))))
        )

        polaritySimplify(newBody, Set(isUnknown), down)
    }
    
}
