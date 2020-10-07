package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.TermOps._

/** Applies the substitution [x -> s] in term t. Will perform alpha-renaming to
  * avoid variable capture when necessary.
  * When creating new variables for alpha-renaming, it will use the given name
  * generator.
  * This for example can be used to make sure when introducing new variables
  * that the substituter avoids a certain set of symbols (e.g. function names
  * that are used in some signature).
  * Note that this will mutate the name generator object.
  * The substituter may also forbid other names inside the name generator
  * to help avoid variable capture.*/
object Substituter {
    def apply(x: Var, s: Term, t: Term, nameGen: NameGenerator): Term = {
        // Forbid all names used in term
        for(name <- t.allSymbols) {
            nameGen.forbidName(name)
        }
        
        val freeVarsOfS = s.freeVarConstSymbols
        
        def sub(t: Term): Term = t match {
            case (v: Var) if (v == x) => s
            case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => t
            case Not(p) => Not(sub(p))
            case AndList(args) => AndList(args.map(sub))
            case OrList(args) => OrList(args.map(sub))
            case Distinct(args) => Distinct(args.map(sub))
            case Implication(p, q) => Implication(sub(p), sub(q))
            case Iff(p, q) => Iff(sub(p), sub(q))
            case Eq(l, r) => Eq(sub(l), sub(r))
            case App(f, args) => App(f, args.map(sub))
            case BuiltinApp(function, args) => BuiltinApp(function, args map sub)
            case Exists(vars, _) if (vars.map(_.variable).contains(x)) => t
            case Forall(vars, _) if (vars.map(_.variable).contains(x)) => t
            case Exists(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body)
                Exists(newVariables, sub(newBody))
            }
            case Forall(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body)
                Forall(newVariables, sub(newBody))
            }
            case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(sub(condition), sub(ifTrue), sub(ifFalse))
        }
        
        def avoidCapture(vars: Seq[AnnotatedVar], body: Term) = {
            // Must avoid variable capture
            // If substituting [y -> s] in (forall x . t) where s contains y
            // as a free variable, we must alpha rename (forall x . t) to
            // (forall z . t[x -> z]) where z is a fresh variable
            // Note that since z is fresh, when making the substitution [x -> z]
            // in t, it is impossible to cause capture, so we can use a faster
            // substituter that does not actively avoid capturing.
            val newVariables = new scala.collection.mutable.ListBuffer[AnnotatedVar]
            val substitutions = scala.collection.mutable.Map[Var, Term]()
            for (av <- vars) {
                if (freeVarsOfS contains av.variable) {
                    val freshVar = Var(nameGen.freshName(av.variable.name))
                    substitutions += (av.variable -> freshVar)
                    newVariables += freshVar of av.sort
                } else {
                    newVariables += av
                }
            }
            if (substitutions.size > 0) {
                val newBody = body.fastSubstitute(substitutions.toMap)
                (newVariables.toList, newBody)
            } else {
                (vars, body)
            }
        }
        
        sub(t)
    }
}

/** Applies the substitutions [x_1 |-> t_1, ..., x_n |-> t_n], given by the map,
  * to term t.
  * The substituter will NOT avoid variable capture; it is the responsibility
  * of the caller to make sure the substitution terms do not contain free
  * variables that could be captured.
  * For example, it would be okay to substitute with domain elements or fresh
  * constants that do not share the same name as any quantified variable.
  * If in doubt, do not use this class. */
object FastSubstituter {
    def apply(substitutions: Map[Var, Term], t: Term): Term = {
        // sigma is the substitution, it can change during recursive calls
        def sub(sigma: Map[Var, Term], t: Term): Term =
            if (sigma.isEmpty) t
            else t match {
                case (v: Var) if (sigma contains v) => sigma(v)
                case Top | Bottom | Var(_) | DomainElement(_, _) | EnumValue(_)
                    | IntegerLiteral(_) | BitVectorLiteral(_, _) => t
                case Not(p) => Not(sub(sigma, p))
                case AndList(args) => AndList(args map (sub(sigma, _)))
                case OrList(args) => OrList(args map (sub(sigma, _)))
                case Distinct(args) => Distinct(args map (sub(sigma, _)))
                case Implication(p, q) => Implication(sub(sigma, p), sub(sigma, q))
                case Iff(p, q) => Iff(sub(sigma, p), sub(sigma, q))
                case Eq(l, r) => Eq(sub(sigma, l), sub(sigma, r))
                case App(f, args) => App(f, args map (sub(sigma, _)))
                case BuiltinApp(f, args) => BuiltinApp(f, args map (sub(sigma, _)))
                case Exists(vars, body) => {
                    // Substitute x->t in (exists x . phi) becomes (exists x . phi)
                    // Remove these from the substitution before recursive call
                    val variables = vars map (_.variable)
                    val sigmaPrime: Map[Var, Term] = sigma.view.filterKeys(!variables.contains(_)).toMap
                    Exists(vars, sub(sigmaPrime, body))
                }
                case Forall(vars, body) => {
                    // Substitute x->t in (forall x . phi) becomes (forall x . phi)
                    // Remove these from the substitution before recursive call
                    val variables = vars.map(_.variable)
                    val sigmaPrime: Map[Var, Term] = sigma.view.filterKeys(!variables.contains(_)).toMap
                    Forall(vars, sub(sigmaPrime, body))
                }
                case IfThenElse(condition, ifTrue, ifFalse) =>
                    IfThenElse(sub(sigma, condition), sub(sigma, ifTrue), sub(sigma, ifFalse))
            }
        
        sub(substitutions, t)
    }
}
