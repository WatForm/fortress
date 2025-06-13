package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.TermOps._

/** Applies the substitution [x -> s] in term t.
 * This substitution is safe with respect to variable capture.
 * An example of variable capture is substituting [x -> s] in Forall s, f(s, x), which 
 * if done naively becomes Forall s, f(s, s).
 * The substituter performs alpha-renaming to avoid this variable capture when necessary.
 * When creating new variables for alpha-renaming, it will use the given name generator.
 * This for example can be used to make sure when introducing new variables that the substituter
 * avoids a certain set of symbols (e.g. function names that are used in some signature).
 * Note that this mutates the name generator object.
 * The substituter may also forbid other names inside the name generator to help avoid variable capture.
 */
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
            case Closure(f, arg1, arg2, args) => Closure(f, sub(arg1), sub(arg2), args map sub)
            case ReflexiveClosure(f, arg1, arg2, args) => ReflexiveClosure(f, sub(arg1), sub(arg2), args map sub)
            case Exists(vars, _) if (vars.map(_.variable).contains(x)) => t
            case Forall(vars, _) if (vars.map(_.variable).contains(x)) => t
            case Exists(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body, freeVarsOfS, nameGen)
                Exists(newVariables, sub(newBody))
            }
            case Forall(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body, freeVarsOfS, nameGen)
                Forall(newVariables, sub(newBody))
            }
            case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(sub(condition), sub(ifTrue), sub(ifFalse))
        }
        
        sub(t)
    }

    def avoidCapture(vars: Seq[AnnotatedVar], body: Term, precomputedFreeVars: Set[Var], nameGen: NameGenerator) = {
            // Must avoid variable capture
            // If substituting [y -> s] in (forall x . t) where s contains x
            // as a free variable, we must alpha rename (forall x . t) to
            // (forall z . t[x -> z]) where z is a fresh variable
            // Note that since z is fresh, when making the substitution [x -> z]
            // in t, it is impossible to cause capture, so we can use a faster
            // substituter that does not actively avoid capturing.
            val newVariables = new scala.collection.mutable.ListBuffer[AnnotatedVar]
            val substitutions = scala.collection.mutable.Map[Var, Term]()
            for (av <- vars) {
                if (precomputedFreeVars contains av.variable) {
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

    def renameApplications(term: Term, original: String, replacement: String): Term = {
        def recur(term: Term): Term = term match {
            case Top | Bottom | Var(_) | EnumValue(_) | BitVectorLiteral(_, _) | IntegerLiteral(_) | DomainElement(_, _) | EnumValue(_) => term
            case AndList(arguments) => AndList(arguments.map(recur))
            case OrList(arguments) => OrList(arguments.map(recur))
            case Distinct(arguments) => Distinct(arguments.map(recur))
            case Implication(left, right) => Implication(recur(left), recur(right))
            case Iff(left, right) => Iff(recur(left), recur(right))
            case Eq(left, right) => Eq(recur(left), recur(right))
            case BuiltinApp(function, arguments) => BuiltinApp(function, arguments.map(recur))
            case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(recur(condition), recur(ifTrue), recur(ifFalse))
            case Not(body) => Not(recur(body))

            case Exists(vars, body) => Exists(vars, recur(body))
            case Forall(vars, body) => Forall(vars, recur(body))
            case Exists2ndOrder(declarations, body) => {
                if(declarations.map(_.name).contains(original)) term
                else Exists2ndOrder(declarations, recur(body))
            }
            case Forall2ndOrder(declarations, body) => {
                if(declarations.map(_.name).contains(original)) term
                else Forall2ndOrder(declarations, recur(body))
            }
            
            case SetCardinality(predicate) => {
                if(predicate == original) SetCardinality(replacement)
                else term
            }
            case Closure(functionName, arg1, arg2, fixedArgs) => {
                val newName = if(functionName == original) replacement else functionName
                Closure(newName, recur(arg1), recur(arg2), fixedArgs.map(recur))
            }
            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
                val newName = if(functionName == original) replacement else functionName
                ReflexiveClosure(newName, recur(arg1), recur(arg2), fixedArgs.map(recur))
            }
            case App(functionName, arguments) => {
                val newName = if(functionName == original) replacement else functionName
                App(newName, arguments.map(recur))
            }
        }
        recur(term)
    }

    def appendToApplications(term: Term, fnName: String, argsToAppend: Seq[Term], nameGen: NameGenerator): Term = {
        // Forbid all names used in term
        for(name <- term.allSymbols) {
            nameGen.forbidName(name)
        }

        val freeVarsOfAppendedArgs = argsToAppend.map(t => t.freeVarConstSymbols).flatten.toSet

        // todo fix variable capture
        def recur(term: Term): Term = term match {
            case Top | Bottom | Var(_) | DomainElement(_, _) | EnumValue(_) | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
            case Distinct(arguments) => Distinct(arguments.map(recur))
            case Iff(left, right) => Iff(recur(left), recur(right))
            case Not(body) => Not(recur(body))
            case Eq(left, right) => Eq(recur(left), recur(right))
            case AndList(arguments) => AndList(arguments.map(recur))
            case OrList(arguments) => OrList(arguments.map(recur))
            case Implication(left, right) => Implication(recur(left), recur(right))
            case BuiltinApp(function, arguments) => BuiltinApp(function, arguments.map(recur))
            case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(recur(condition), recur(ifTrue), recur(ifFalse))

            case Exists(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body, freeVarsOfAppendedArgs, nameGen)
                Exists(newVariables, recur(newBody))
            }
            case Forall(vars, body) => {
                val (newVariables, newBody) = avoidCapture(vars, body, freeVarsOfAppendedArgs, nameGen)
                Forall(newVariables, recur(newBody))
            }
            case Exists2ndOrder(declarations, body) => Exists2ndOrder(declarations, recur(body))
            case Forall2ndOrder(declarations, body) => Forall2ndOrder(declarations, recur(body))
                
            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
                if(functionName == fnName) ReflexiveClosure(functionName, recur(arg1), recur(arg2), fixedArgs.map(recur) ++ argsToAppend)
                else ReflexiveClosure(functionName, recur(arg1), recur(arg2), fixedArgs.map(recur))
            }
            case Closure(functionName, arg1, arg2, fixedArgs) => {
                if(functionName == fnName) Closure(functionName, recur(arg1), recur(arg2), fixedArgs.map(recur) ++ argsToAppend)
                else Closure(functionName, recur(arg1), recur(arg2), fixedArgs.map(recur))
            }
            case App(functionName, arguments) => {
                if(functionName == fnName) App(functionName, arguments.map(recur) ++ argsToAppend)
                else App(functionName, arguments.map(recur))
            }

            case SetCardinality(predicate) => term
        }
        recur(term)
    }
}

/** Applies the substitutions [x_1 |-> t_1, ..., x_n |-> t_n], given by the map, to term t.
 * These substitutions are done simultaneously, not in sequence.
 * The substituter will NOT avoid variable capture.
 * An example of variable capture is substituting [x -> s] in Forall s, f(s, x), which 
 * if done naively becomes Forall s, f(s, s).
 * It is the responsibility of the caller to make sure the substitution replacements do not contain free
 * variables that could be captured.
 * For example, it would be okay to substitute with domain elements or fresh constants that do not share
 * the same name as any quantified variable.
 * If in doubt, do not use this class.
 */
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
                case Closure(f, arg1, arg2, args) => Closure(f, sub(sigma, arg1), sub(sigma, arg2), args map (sub(sigma, _)))
                case ReflexiveClosure(f, arg1, arg2, args) => ReflexiveClosure(f, sub(sigma, arg1), sub(sigma, arg2), args map (sub(sigma, _)))
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