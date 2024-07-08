package fortress.operations

import fortress.msfol._

object IntegerPredicateFinder {
    /**
      * Checks to see if a term contains an integer or bitvector predicate (EQ, Comparisons, or user-defined)
      *
      * @param baseTerm the term to search
      * @param intVars variables, constants, etc that are integers or bitvectors
      * @param integerPredicates Names of user-specified functions that are integer predicates
      */
    def containsIntegerPredicate(baseTerm: Term, intVars: Set[Var] = Set.empty, integerPredicates: Set[String]): Boolean = {
        
        def hasIntPredicate(term: Term, integerVars: Set[Var] = Set.empty): Boolean = {
            // any predicate which contains an integer must at some point in that path contain an integer predicate
            term match {
                case _: LeafTerm => false

                case BuiltinApp(func, args) => func match {
                    case _: BinaryIntegerRelation => true
                    case _: BinaryBitVectorRelation => true
                    case _ => false
                }
                case App(functionName, terms) => integerPredicates.contains(functionName) || terms.exists(hasIntPredicate(_,integerVars))

                case Exists(annotatedVars, body) => {
                    val (vars, sorts) = annotatedVars.map({case AnnotatedVar(variable, sort) => (variable, sort)}).unzip

                    // If an int sort or a bitvector sort is here, just return true
                    if (sorts.contains(IntSort) || sorts.exists({case BitVectorSort(_) => true case _ => false})){
                        true
                    } else{
                        // vars are not integers if they are overridden here
                        hasIntPredicate(body, integerVars.diff(vars.toSet))
                    } 
                }
                case Forall(annotatedVars, body) => {
                    val (vars, sorts) = annotatedVars.map({case AnnotatedVar(variable, sort) => (variable, sort)}).unzip

                    // If an int sort or a bitvector sort is here, just return true
                    if (sorts.contains(IntSort) || sorts.exists({case BitVectorSort(_) => true case _ => false})){
                        true
                    } else{
                        // vars are not integers if they are overridden here
                        hasIntPredicate(body, integerVars.diff(vars.toSet))
                    } 
                }

                case OrList(terms) => terms.exists(hasIntPredicate(_,integerVars))
                case AndList(terms) => terms.exists(hasIntPredicate(_,integerVars))
                case Closure(_, arg1, arg2, fixedArgs) => (fixedArgs :+ arg1 :+ arg2).exists(hasIntPredicate(_,integerVars))
                case ReflexiveClosure(_, arg1, arg2, fixedArgs) => (fixedArgs :+ arg1 :+ arg2).exists(hasIntPredicate(_,integerVars))
                case Distinct(terms) => terms.exists(hasIntPredicate(_,integerVars))
                case Implication(left, right) => hasIntPredicate(left, integerVars) || hasIntPredicate(right, integerVars)
                case Not(body) => hasIntPredicate(body, integerVars)
                case Eq(left, right) => hasInteger(left, integerVars) || hasInteger(right, integerVars)
                case Iff(left, right) => hasIntPredicate(left, integerVars) || hasIntPredicate(right, integerVars)
                case IfThenElse(condition, ifTrue, ifFalse) => hasIntPredicate(condition, integerVars) || hasIntPredicate(ifTrue, integerVars) || hasIntPredicate(ifFalse, integerVars)
            }
        }
        def hasInteger(term: Term, integerVars: Set[Var]): Boolean = {
            term match {
                case BitVectorLiteral(_, _) => true
                case IntegerLiteral(_) => true
                case x: Var => integerVars contains x 
                case _: LeafTerm => false

                // we just assume any quantifier using an integer is actually going to use it.
                case Exists(annotatedVars, body) => {
                    val (vars, sorts) = annotatedVars.map({case AnnotatedVar(variable, sort) => (variable, sort)}).unzip

                    // If an int sort or a bitvector sort is here, just return true
                    if (sorts.contains(IntSort) || sorts.exists({case BitVectorSort(_) => true case _ => false})){
                        true
                    } else{
                        // vars are not integers if they are overridden here
                        hasInteger(body, integerVars.diff(vars.toSet))
                    } 
                }
                case Forall(annotatedVars, body) => {
                    val (vars, sorts) = annotatedVars.map({case AnnotatedVar(variable, sort) => (variable, sort)}).unzip

                    // If an int sort or a bitvector sort is here, just return true
                    if (sorts.contains(IntSort) || sorts.exists({case BitVectorSort(_) => true case _ => false})){
                        true
                    } else{
                        // vars are not integers if they are overridden here
                        hasInteger(body, integerVars.diff(vars.toSet))
                    } 
                }
                
                case OrList(terms) => terms.exists(hasInteger(_,integerVars))
                case AndList(terms) => terms.exists(hasInteger(_,integerVars))
                case Closure(_, arg1, arg2, fixedArgs) => (fixedArgs :+ arg1 :+ arg2).exists(hasInteger(_,integerVars))
                case ReflexiveClosure(_, arg1, arg2, fixedArgs) => (fixedArgs :+ arg1 :+ arg2).exists(hasInteger(_,integerVars))
                case Distinct(terms) => terms.exists(hasInteger(_,integerVars))
                case IfThenElse(cTerm, tTerm, fTerm) => Seq(cTerm, tTerm, fTerm).exists(hasInteger(_,integerVars))
                case Iff(left, right) => hasInteger(left, integerVars) || hasInteger(right, integerVars)
                case BuiltinApp(_, terms) => terms.exists(hasInteger(_,integerVars))
                case App(functionName, terms) => terms.exists(hasInteger(_,integerVars))
                case Not(body) => hasInteger(body, integerVars)
                case Eq(left, right) => hasInteger(left, integerVars) || hasInteger(right, integerVars)
                case Implication(left, right) => hasInteger(left, integerVars) || hasInteger(right, integerVars)
            }
        }

        hasIntPredicate(baseTerm, intVars)
    }

    

    

}