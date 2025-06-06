package fortress.operations

import fortress.msfol._
import fortress.operations.TermOps._

object Simplifier {
    def simplify(term: Term): Term = {
        def simplifyFull(term: Term): Term = term match {
            case Not(body) => simplifyStep(Not(simplifyFull(body)))
            case AndList(args) => simplifyStep(AndList(args.map(simplifyFull)))
            case OrList(args) => simplifyStep(OrList(args.map(simplifyFull)))
            case Implication(left, right) => simplifyStep(Implication(simplifyFull(left), simplifyFull(right)))
            case Iff(left, right) => simplifyStep(Iff(simplifyFull(left), simplifyFull(right)))
            case Distinct(args) => simplifyStep(Distinct(args.map(simplifyFull)))
            case Exists(vars, body) => simplifyStep(Exists(vars, simplifyFull(body)))
            case Forall(vars, body) => simplifyStep(Forall(vars, simplifyFull(body)))
            case Eq(left, right) => simplifyStep(Eq(simplifyFull(left), simplifyFull(right)))
            case App(name, args) => simplifyStep(App(name, args.map(simplifyFull)))
            case BuiltinApp(op, args) => simplifyStep(BuiltinApp(op, args.map(simplifyFull)))
            case Closure(name, arg1, arg2, fixedArgs) =>
                simplifyStep(Closure(name, simplifyFull(arg1), simplifyFull(arg2), fixedArgs.map(simplifyFull)))
            case ReflexiveClosure(name, arg1, arg2, fixedArgs) =>
                simplifyStep(ReflexiveClosure(name, simplifyFull(arg1), simplifyFull(arg2), fixedArgs.map(simplifyFull)))
            case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
                 | IntegerLiteral(_) | BitVectorLiteral(_, _) | SetCardinality(_) => term
            case IfThenElse(condition, ifTrue, ifFalse) => simplifyStep(
                IfThenElse(simplifyFull(condition), simplifyFull(ifTrue), simplifyFull(ifFalse))
            )
        }

        simplifyFull(term)
    }

    def simplifyStep(term: Term): Term = term match {
        case Not(Bottom) => Top
        case Not(Top) => Bottom
        case Not(Not(body)) => body
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
        case Implication(Top, p) => p
        case Implication(p, Bottom) => Not(p)
        case Iff(p, Top) => p
        case Iff(Top, p) => p
        case Iff(p, Bottom) => Not(p)
        case Iff(Bottom, p) => Not(p)
        case Eq(d1 @ DomainElement(_, _), d2 @ DomainElement(_, _)) => if (d1 == d2) Top else Bottom
        case Eq(x @ Var(xname), y @ Var(yname)) => {
            if(x == y) Top
            else (DomainElement.interpretName(xname), DomainElement.interpretName(yname)) match {
                case (Some(xde), Some(yde)) if (xde != yde) => Bottom
                case _ => term
            }
        }
        case Eq(left, right) => if (left == right) Top else term
        // Note that we don't need a signature to check below whether the free
        // variable is really free or a constant. We just want to check if
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
        case IfThenElse(Top, ifTrue, ifFalse) => ifTrue
        case IfThenElse(Bottom, ifTrue, ifFalse) => ifFalse
        case IfThenElse(_, Top, Top) => Top
        case IfThenElse(_, Bottom, Bottom) => Bottom
        case _ => term
    }
}