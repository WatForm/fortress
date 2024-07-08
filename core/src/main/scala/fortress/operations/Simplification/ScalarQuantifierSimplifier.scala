package fortress.operations

import fortress.msfol._
import fortress.operations.TermOps._

/**
  * Simplify:
  *   "forall x: A | x = e => f" to "e = e => f[e/x]"
  *   "exists x: A | x = e && f" to "e = e && f[e/x]"
  * There are redundant equalities left over; a further simplifier should take care of them.
  */
object ScalarQuantifierSimplifier extends NaturalTermRecursion {
    def simplify(term: Term): Term = naturalRecur(term)

    override val exceptionalMappings: PartialFunction[Term, Term] = {
        case Forall(vars, or @ OrList(_)) => processForall(vars, extractDisjuncts(naturalRecur(or)))
        case Exists(vars, and @ AndList(_)) => processExists(vars, extractConjuncts(naturalRecur(and)))
    }

    private def extractDisjuncts(term: Term): Seq[Term] = term match {
        case OrList(disjuncts) => disjuncts flatMap extractDisjuncts
        case Not(negated) => extractConjuncts(negated) map negate  // de Morgan's laws
        case _ => Seq(term)
    }

    private def extractConjuncts(term: Term): Seq[Term] = term match {
        case AndList(conjuncts) => conjuncts flatMap extractConjuncts
        case Not(negated) => extractDisjuncts(negated) map negate  // de Morgan's laws
        case _ => Seq(term)
    }

    private def negate(term: Term) = term match {
        case Not(sub) => sub
        case _ => Not(term)
    }

    private def processForall(vars: Seq[AnnotatedVar], disjuncts: Seq[Term]): Term = {
        // for each var x, if "x != e" appears in the disjuncts, substitute e for x in all disjuncts
        // note that x must not appear free in e
        var remainingDisjuncts = disjuncts
        val remainingVars = vars filter { case AnnotatedVar(variable, _) =>
            val substitutableExprs = remainingDisjuncts collect {
                case Not(Eq(v, e)) if v == variable
                    && !(e.freeVarConstSymbols contains variable) => e
                case Not(Eq(e, v)) if v == variable
                    && !(e.freeVarConstSymbols contains variable) => e
            }
            if (substitutableExprs.nonEmpty) {
                // just pick the first one
                val expr = substitutableExprs.head
                remainingDisjuncts = substituteAll(remainingDisjuncts, variable, expr)
            }
            substitutableExprs.isEmpty
        }

        val body = Or.smart(remainingDisjuncts)
        if (remainingVars.isEmpty) body
        else Forall(remainingVars, body)
    }

    private def processExists(vars: Seq[AnnotatedVar], conjuncts: Seq[Term]): Term = {
        // for each var x, if "x = e" appears in the conjuncts, substitute e for x in all conjuncts
        // note that x must not appear free in e
        var remainingConjuncts = conjuncts
        val remainingVars = vars filter { case AnnotatedVar(variable, _) =>
            val substitutableExprs = remainingConjuncts collect {
                case Eq(v, e) if v == variable
                    && !(e.freeVarConstSymbols contains variable) => e
                case Eq(e, v) if v == variable
                    && !(e.freeVarConstSymbols contains variable) => e
            }
            if (substitutableExprs.nonEmpty) {
                // just pick the first one
                val expr = substitutableExprs.head
                remainingConjuncts = substituteAll(remainingConjuncts, variable, expr)
            }
            substitutableExprs.isEmpty
        }

        val body = And.smart(remainingConjuncts)
        if (remainingVars.isEmpty) body
        else Exists(remainingVars, body)
    }

    private def substituteAll(terms: Seq[Term], variable: Var, expr: Term): Seq[Term] =
        terms map { _.substitute(variable, expr) }
}
