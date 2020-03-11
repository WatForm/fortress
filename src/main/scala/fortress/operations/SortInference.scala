package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import scala.collection.mutable
import fortress.data._

case class Equation(x: Sort, y: Sort)

object SortInference {
    
    type ContextStack = List[(String, Sort)]
    
    def mostGeneralSortedTheory(theory: Theory): Theory = {
        /** 
            Booleans don't need to be factored into equation solving.
            Only solve equations between type variables.
        */
        var index = 0
        def freshInt(): Int = {
            val temp = index
            index += 1
            temp
        }
        
        def sortVar(index: Int): SortConst = SortConst(index.toString)
        
        // Associate each constant with a fresh sort variable
        val constantMap: mutable.Map[String, Sort] = mutable.Map.empty
        for(c <- theory.constants) {
            c.sort match {
                case BoolSort => {
                    constantMap += (c.name -> BoolSort)
                }
                case SortConst(_) => {
                    constantMap += ( c.name -> sortVar(freshInt()) )
                }
                case _ => ???
            }
        }
        
        // Associate each function with a collection of sorts
        val fnMap: mutable.Map[String, (Seq[Sort], Sort)] = mutable.Map.empty
        for(f <- theory.functionDeclarations) {
            Errors.precondition(f.argSorts.forall(!_.isBuiltin))
            val args = f.argSorts map (sort => sortVar(freshInt()))
            val result = f.resultSort match {
                case BoolSort => BoolSort
                case SortConst(_) => sortVar(freshInt())
                case _ => ???
            }
            fnMap += (f.name -> (args, result))
        }
        
        // Replace types on terms with fresh type vars
        def replace(term: Term): Term = term match {
            case Top | Bottom | Var(_)  => term
            case Not(p) => Not(replace(term))
            case AndList(args) => AndList(args map replace)
            case OrList(args) => OrList(args map replace)
            case Distinct(args) => Distinct(args map replace)
            case Implication(p, q) => Implication(replace(p), replace(q))
            case Iff(p, q) => Iff(replace(p), replace(q))
            case Eq(l, r) => Eq(replace(l), replace(r))
            case App(name, args) => App(name, args map replace)
            case Exists(avars, body) => {
                val newVars = avars map {avar => Var(avar.name) of sortVar(freshInt())}
                Exists(newVars, replace(body))
            }
            case Forall(avars, body) => {
                val newVars = avars map {avar => Var(avar.name) of sortVar(freshInt())}
                Forall(newVars, replace(body))
            }
            case EnumValue(_) | DomainElement(_, _) | BuiltinApp(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => ???
        }
        
        // Gather equations
        
        def lookup(name: String, context: ContextStack): Option[Sort] = context match {
            case Nil => None
            case (`name`, sort) :: tail => Some(sort)
            case _ :: tail => lookup(name, tail)
        }
        
        def recur(term: Term, context: ContextStack): (Sort, Set[Equation]) = term match {
            case Top => (BoolSort, Set.empty)
            case Bottom => (BoolSort, Set.empty)
            case Var(name) => lookup(name, context) match {
                case Some(sort) => (sort, Set.empty)
                case None => (constantMap(name), Set.empty)
            }
            case EnumValue(_) => ???
            case Not(p) => {
                val (sort, eqns) = recur(p, context)
                Errors.assertion(sort == BoolSort)
                (BoolSort, eqns)
            }
            case AndList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == BoolSort))
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, eqns.toSet)
            }
            case OrList(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == BoolSort))
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, eqns.toSet)
            }
            case Distinct(args) => {
                val recurInfo = args map {recur(_, context)}
                Errors.assertion(recurInfo forall (_._1 == BoolSort))
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, eqns.toSet)
            }
            case Implication(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(p, context)
                Errors.assertion(pSort == BoolSort)
                Errors.assertion(qSort == BoolSort)
                (BoolSort, pEqns union qEqns)
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(p, context)
                Errors.assertion(pSort == BoolSort)
                Errors.assertion(qSort == BoolSort)
                (BoolSort, pEqns union qEqns)
            }
            case Eq(l, r) => {
                val (lSort, lEqns) = recur(l, context)
                val (rSort, rEqns) = recur(r, context)
                Errors.assertion(lSort != BoolSort)
                Errors.assertion(rSort != BoolSort)
                // Add this to equations!
                (BoolSort, (lEqns union rEqns) + Equation(lSort, rSort) )
            }
            case App(name, args) => {
                val (argSorts, resSort) = fnMap(name)
                Errors.assertion(argSorts.size == args.size)
                val recurInfo = args map {recur(_, context)}
                val recurArgSorts = recurInfo map (_._1)
                val recurEqns = recurInfo flatMap (_._2)
                
                // Add to equations that the argument sorts must match up
                val newEqns = for((sort1, sort2) <- argSorts zip recurArgSorts)
                    yield Equation(sort1, sort2)
                
                val eqns = (recurEqns ++ newEqns).toSet
                (resSort, eqns)
            }
            case Exists(avars, body) => {
                // Give the annotated vars fresh variables
                val freshVars: List[(String, Sort)] =
                    (avars map {av => (av.name, sortVar(freshInt()))}).toList
                // Must put variables on context stack in reverse
                // e.g. (forall v: A v: B, p(v)), the context should be
                // List[v: B, v: A]
                val newContext = freshVars.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.precondition(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case Forall(avars, body) => {
                // Give the annotated vars fresh variables
                val freshVars: List[(String, Sort)] =
                    (avars map {av => (av.name, sortVar(freshInt()))}).toList
                // Must put variables on context stack in reverse
                // e.g. (forall v: A v: B, p(v)), the context should be
                // List[v: B, v: A]
                val newContext = freshVars.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.precondition(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case DomainElement(_, _) => ???
            case BuiltinApp(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
        }
        
        val recurInfo = theory.axioms map {recur(_, Nil)}
        val recurSorts = recurInfo map (_._1)
        Errors.assertion(recurSorts forall (_ == BoolSort))
        val equations = (recurInfo flatMap (_._2)).toList
        
        // Solve Equations
        val unionFind = new SimpleUnionFind
        for(Equation(lsort, rsort) <- equations) {
            (lsort, rsort) match {
                case (lsort: SortConst, rsort: SortConst) => {
                    val lInt = lsort.name.toInt
                    val rInt = rsort.name.toInt
                    unionFind.union(lInt, rInt)
                }
                case _ => ???
            }
        }
        
        // Substitute sorts
        def subSort(sort: Sort): Sort = sort match {
            case SortConst(indexStr) => {
                val index = indexStr.toInt
                val repr = unionFind.find(index)
                sortVar(repr)
            }
            case BoolSort => BoolSort
            case _ => ???
        }
        
        val newConstants: Set[AnnotatedVar] = theory.constants map (av => {
            Var(av.name) of subSort(constantMap(av.name))
        })
        
        val newFunctions: Set[FuncDecl] = theory.functionDeclarations map (f => {
            val (argSorts, resSort) = fnMap(f.name)
            val newArgSorts = argSorts map subSort
            val newResSort = subSort(resSort)
            FuncDecl(f.name, newArgSorts, newResSort)
        })
        
        def subTerm(term: Term): Term = term match {
            case Top | Bottom | Var(_)  => term
            case Not(p) => Not(subTerm(term))
            case AndList(args) => AndList(args map subTerm)
            case OrList(args) => OrList(args map subTerm)
            case Distinct(args) => Distinct(args map subTerm)
            case Implication(p, q) => Implication(subTerm(p), subTerm(q))
            case Iff(p, q) => Iff(subTerm(p), subTerm(q))
            case Eq(l, r) => Eq(subTerm(l), subTerm(r))
            case App(name, args) => App(name, args map subTerm)
            case Exists(avars, body) => {
                val newVars = avars map {avar => Var(avar.name) of subSort(avar.sort)}
                Exists(newVars, subTerm(body))
            }
            case Forall(avars, body) => {
                val newVars = avars map {avar => Var(avar.name) of subSort(avar.sort)}
                Forall(newVars, subTerm(body))
            }
            case EnumValue(_) | DomainElement(_, _) | BuiltinApp(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => ???
        }
        
        val newAxioms: Set[Term] = theory.axioms map subTerm
        
        val usedSorts: Set[Sort] = { for(i <- 0 to (index - 1)) yield sortVar(unionFind.find(i)) }.toSet
        
        Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstants(newConstants)
            .withFunctionDeclarations(newFunctions)
            .withAxioms(newAxioms)
    }
    
}
