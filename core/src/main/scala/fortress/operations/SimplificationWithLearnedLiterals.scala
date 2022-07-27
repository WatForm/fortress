package fortress.operations

import fortress.msfol._
import fortress.operations.TermOps._

object SimplifierWithLearnedLiterals {
    def simplify(term: Term, learnedLiterals: Map[Term,LeafTerm]): Term = {
        def simplifyFull(term: Term): Term = term match {
            case Not(body) => simplifyStep(Not(simplifyFull(body)), learnedLiterals)
            case AndList(args) => simplifyStep(AndList(args.map(simplifyFull)), learnedLiterals)
            case OrList(args) => simplifyStep(OrList(args.map(simplifyFull)), learnedLiterals)
            case Implication(left, right) => simplifyStep(Implication(simplifyFull(left), simplifyFull(right)), learnedLiterals)
            case Iff(left, right) => simplifyStep(Iff(simplifyFull(left), simplifyFull(right)), learnedLiterals)
            case Distinct(args) => simplifyStep(Distinct(args.map(simplifyFull)), learnedLiterals)
            case Exists(vars, body) => simplifyStep(Exists(vars, simplifyFull(body)), learnedLiterals)
            case Forall(vars, body) => simplifyStep(Forall(vars, simplifyFull(body)), learnedLiterals)
            // We consider applications, equals and closures to be atomic and have non-Boolean arguments
            // so we need not recurse on their arguments
            case Eq(_, _) | App(_, _) | BuiltinApp(_, _) | Closure(_, _, _)
                | ReflexiveClosure(_, _, _) => simplifyStep(term, learnedLiterals)
            case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
            case IfThenElse(condition, ifTrue, ifFalse) => simplifyStep(
                IfThenElse(simplifyFull(condition), simplifyFull(ifTrue), simplifyFull(ifFalse)), learnedLiterals
            )
        }
        
        simplifyFull(term)
    }
    
    def simplifyStep(term: Term, learnedLiterals: Map[Term,LeafTerm]): Term = term match {
        case Not(Bottom) => Top
        case Not(Top) => Bottom
        case Not(Not(body)) => learnedLiterals getOrElse (body, body)
        case AndList(args) => {
            if (args contains Bottom) Bottom
            else {
                val newArgs = args filter (_ != Top)
                And.smart(newArgs.distinct)
            }
        }
        case OrList(args) => {
            if (args contains Top) Top
            else {
                val newArgs = args.filter(_ != Bottom)
                Or.smart(newArgs.distinct)
            }
        }
        case Implication(Bottom, _) => Top
        case Implication(_, Top) => Top
        case Implication(Top, p) => learnedLiterals getOrElse (p, p)
        case Implication(p, Bottom) => Not(learnedLiterals getOrElse (p, p))
        case Iff(p, Top) => learnedLiterals getOrElse (p, p)
        case Iff(Top, p) => learnedLiterals getOrElse (p, p)
        case Iff(p, Bottom) => Not(learnedLiterals getOrElse (p, p))
        case Iff(Bottom, p) => Not(learnedLiterals getOrElse (p, p))
        case Eq(d1 @ DomainElement(_, _), d2 @ DomainElement(_, _)) => if (d1 == d2) Top else Bottom
        case Eq(x @ Var(xname), y @ Var(yname)) => {
            if(x == y) Top
            else (DomainElement.interpretName(xname), DomainElement.interpretName(yname)) match {
                case (Some(xde), Some(yde)) if (xde != yde) => Bottom
                case _ => term
            }
        }
        case Eq(left, right) => if (left == right) Top else learnedLiterals getOrElse (term, term)
        // Note that we don't need a signature to check below whether the free
        // free variable is really or a constant. We just want to check if
        // the quantified variable x is within the set of free vars.
        // If x is within free vars union constants, then since it is quantified
        // here it must be a free var.
        case Exists(vars, body) => {
            // For non-empty domains, if x \notin phi, then (exists x . phi) is equiv to phi
            val freeVars: Set[Var] = body.freeVarConstSymbols
            val newVars = vars filter (freeVars contains _.variable)
            if (newVars.size == 0) body
            else Exists(newVars, body)
        }
        case Forall(vars, body) => {
            // For non-empty domains, if x \notin phi, then (forall x . phi) is equiv to phi
            val freeVars: Set[Var] = body.freeVarConstSymbols
            val newVars = vars filter (freeVars contains _.variable)
            if (newVars.size == 0) body
            else Forall(newVars, body)
        }
        case IfThenElse(Top, ifTrue, ifFalse) => learnedLiterals getOrElse (ifTrue, ifTrue)
        case IfThenElse(Bottom, ifTrue, ifFalse) => learnedLiterals getOrElse (ifFalse, ifFalse)
        case _ => learnedLiterals getOrElse (term, term)
    }
}
