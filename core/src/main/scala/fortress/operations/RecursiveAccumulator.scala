package fortress.operations

import fortress.msfol._

object RecursiveAccumulator {
    /** Accumulates the set of all symbol names used in the term, including free
      * variables and constants, bound variables (even useless ones that aren't
      * used in the body of the quantifier), function names, and sort names that
      * appear on variable bindings. */
    def allSymbolsIn(term: Term): Set[String] = term match {
        case Top | Bottom | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case Var(x) => Set(x)
        case EnumValue(x) => Set(x)
        case Not(p) => allSymbolsIn(p)
        case AndList(args) => (args map allSymbolsIn) reduce (_ union _)
        case OrList(args) => (args map allSymbolsIn) reduce (_ union _)
        case Distinct(args) => (args map allSymbolsIn) reduce (_ union _)
        case Implication(p, q) => allSymbolsIn(p) union allSymbolsIn(q)
        case Iff(p, q) => allSymbolsIn(p) union allSymbolsIn(q)
        case Eq(l, r) => allSymbolsIn(l) union allSymbolsIn(r)
        case App(fname, args) => ( (args map allSymbolsIn) reduce (_ union _) ) + fname
        case BuiltinApp(function, args) => (args map allSymbolsIn) reduce (_ union _)
        case Closure(fname, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map allSymbolsIn) reduce (_ union _)) + fname
        case ReflexiveClosure(fname, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map allSymbolsIn) reduce (_ union _)) + fname
        case Forall(vars, body) => allSymbolsIn(body) union (vars map (_.variable.name)).toSet union (vars map (_.sort.name)).toSet
        case Exists(vars, body) => allSymbolsIn(body) union (vars map (_.variable.name)).toSet union (vars map (_.sort.name)).toSet
        case IfThenElse(condition, ifTrue, ifFalse) => allSymbolsIn(condition) union allSymbolsIn(ifTrue) union allSymbolsIn(ifFalse)
    }
    
    /** Returns the set of all domain elements that appear within a term.
    An exception is thrown if the term contains EnumValues, since you are probably
    missing a step in the pipeline if there are still enum values but you care about
    which domain elements exist. */
    def domainElementsIn(term: Term): Set[DomainElement] = term match {
        case Top | Bottom | Var(_) 
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case de @ DomainElement(_, _) => Set(de)
        case EnumValue(_) => ???
        case Not(p) => domainElementsIn(p)
        case AndList(args) => args.map(domainElementsIn).reduce((a, b) => a union b)
        case OrList(args) => args.map(domainElementsIn).reduce((a, b) => a union b)
        case Distinct(args) => args.map(domainElementsIn).reduce((a, b) => a union b)
        case Implication(p, q) => domainElementsIn(p) union domainElementsIn(q)
        case Iff(p, q) => domainElementsIn(p) union domainElementsIn(q)
        case Eq(l, r) => domainElementsIn(l) union domainElementsIn(r)
        case App(fname, args) => args.map(domainElementsIn).reduce((a, b) => a union b)
        case BuiltinApp(function, args) => args.map(domainElementsIn).reduce((a, b) => a union b)
        case Closure(_, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map domainElementsIn) reduce (_ union _))
        case ReflexiveClosure(_, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map domainElementsIn) reduce (_ union _))
        case Forall(vars, body) => domainElementsIn(body)
        case Exists(vars, body) => domainElementsIn(body)
        case IfThenElse(condition, ifTrue, ifFalse) => domainElementsIn(condition) union domainElementsIn(ifTrue) union domainElementsIn(ifFalse)
    }
    

    object EnumValueAccumulator extends NaturalSetAccumulation[EnumValue] {
            override val exceptionalMappings: PartialFunction[Term, Set[EnumValue]] = {
                case e @ EnumValue(_) => Set(e)
            }
            
            def apply(term: Term): Set[EnumValue] = naturalRecur(term)
    }
    def enumValuesIn(term: Term): Set[EnumValue] = {
        EnumValueAccumulator(term)
    }
    
    def functionsIn(term: Term): Set[String] = term match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case Not(p) => functionsIn(p)
        case AndList(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case OrList(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Distinct(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Implication(p, q) => functionsIn(p) union functionsIn(q)
        case Iff(p, q) => functionsIn(p) union functionsIn(q)
        case Eq(l, r) => functionsIn(l) union functionsIn(r)
        case App(fname, args) => args.map(functionsIn).reduce((a, b) => a union b) + fname
        case BuiltinApp(function, args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Closure(fname, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map functionsIn) reduce (_ union _)) + fname
        case ReflexiveClosure(fname, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map functionsIn) reduce (_ union _)) + fname
        case Forall(vars, body) => functionsIn(body)
        case Exists(vars, body) => functionsIn(body)
        case IfThenElse(condition, ifTrue, ifFalse) => functionsIn(condition) union functionsIn(ifTrue) union functionsIn(ifFalse)
    }
    
    def constantsIn(term: Term): Set[String] = {
        def recur(t: Term, variables: Set[String]): Set[String] = t match {
            case Top | Bottom | DomainElement(_, _) | EnumValue(_)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set.empty
            case Var(x) if (! (variables contains x)) => Set(x)
            case Var(x) => Set.empty
            case Not(p) => recur(p, variables)
            case AndList(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case OrList(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Distinct(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Implication(p, q) => recur(p, variables) union recur(q, variables)
            case Iff(p, q) => recur(p, variables) union recur(q, variables)
            case Eq(l, r) => recur(l, variables) union recur(r, variables)
            case App(fname, args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case BuiltinApp(function, args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Closure(fname, arg1, arg2, args) => (args :+ arg1 :+ arg2).map(recur(_, variables)) reduce (_ union _)
            case ReflexiveClosure(fname, arg1, arg2, args) => (args :+ arg1 :+ arg2).map(recur(_, variables)) reduce (_ union _)
            case Forall(vars, body) => recur(body, variables ++ vars.map(_.name))
            case Exists(vars, body) => recur(body, variables ++ vars.map(_.name))
            case IfThenElse(condition, ifTrue, ifFalse) => constantsIn(condition) union constantsIn(ifTrue) union constantsIn(ifFalse)
        }
        recur(term, Set.empty)
    }
    
    /** Accumulates the free variables of a term. Note that this only considers the
      * term as a block of syntax, without respect to a signature, so a free variable
      * here may be bound as a constant of a theory. */
    def freeVariablesIn(term: Term): Set[Var] = term match {
        case Top | Bottom | DomainElement(_, _) | EnumValue(_)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case v @ Var(x) => Set(v)
        case Not(p) => freeVariablesIn(p)
        case AndList(args) => (args map freeVariablesIn) reduce (_ union _)
        case OrList(args) => (args map freeVariablesIn) reduce (_ union _)
        case Distinct(args) => (args map freeVariablesIn) reduce (_ union _)
        case Implication(p, q) => freeVariablesIn(p) union freeVariablesIn(q)
        case Iff(p, q) => freeVariablesIn(p) union freeVariablesIn(q)
        case Eq(l, r) => freeVariablesIn(l) union freeVariablesIn(r)
        case App(fname, args) => (args map freeVariablesIn) reduce (_ union _)
        case BuiltinApp(function, args) => (args map freeVariablesIn) reduce (_ union _)
        case Closure(_, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map freeVariablesIn) reduce (_ union _))
        case ReflexiveClosure(_, arg1, arg2, args) => (((args :+ arg1 :+ arg2) map freeVariablesIn) reduce (_ union _))
        case Exists(vars, body) => freeVariablesIn(body) diff (vars map (_.variable)).toSet
        case Forall(vars, body) => freeVariablesIn(body) diff (vars map (_.variable)).toSet
        case IfThenElse(condition, ifTrue, ifFalse) => freeVariablesIn(condition) union freeVariablesIn(ifTrue) union freeVariablesIn(ifFalse)
    }
}
