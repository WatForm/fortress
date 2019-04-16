package fortress.tfol.operations

import fortress.tfol._
import fortress.data.NameGenerator;

import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // Use immutable seq

/** Applies the substitution [x -> s] in term t. will perform alpha-renaming to
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
            case Top() | Bottom() | Var(_) | DomainElement(_, _) => t
            case Not(p) => Not(sub(p))
            case AndList(args) => AndList(args.map(sub))
            case OrList(args) => OrList(args.map(sub))
            case Distinct(args) => Distinct(args.map(sub))
            case Implication(p, q) => Implication(sub(p), sub(q))
            case Iff(p, q) => Iff(sub(p), sub(q))
            case Eq(l, r) => Eq(sub(l), sub(r))
            case App(f, args) => App(f, args.map(sub))
            case TC(r, arg1, arg2) => App(r, sub(arg1), sub(arg2))
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
        }
        
        def avoidCapture(vars: Seq[AnnotatedVar], body: Term) = {
            // Must avoid variable capture
            // If substituting [y -> s] in (forall x . t) where s contains y
            // as a free variable, we must alpha rename (forall x . t) to
            // (forall z . t[x -> z]) where z is a fresh variable
            // Note that since z is fresh, when making the substitution [x -> z]
            // in t, it is impossible to cause capture, so we can use a faster
            // "reckless" substituter that does not actively avoid capturing.
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
                val newBody = body.recklessSubstitute(substitutions.asJava)
                (newVariables.toList, newBody)
            } else {
                (vars, body)
            }
        }
        
        sub(t)
    }
}
