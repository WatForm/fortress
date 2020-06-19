package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import scala.collection.mutable
import fortress.data._
import scala.language.implicitConversions

case class Equation(x: Sort, y: Sort)

object SortInference {
    
    type ContextStack = List[AnnotatedVar]
    
    def inferSorts(theory: Theory): (Theory, SortSubstitution) = {
        /** 
            Booleans don't need to be factored into equation solving.
            Only solve equations between type variables.
        */
        def sortVar(index: Int): SortConst = SortConst(index.toString)
        
        object freshSubstitution extends SortApplication {
            var index = 0
            def freshInt(): Int = {
                val temp = index
                index += 1
                temp
            }
            
            override def apply(sort: Sort) = sort match {
                case SortConst(_) => sortVar(freshInt())
                case sort => sort
            }
        }
        
        // Associate each constant with a fresh sort variable
        val constantMap: Map[String, Sort] = theory.constants.map {c => c.name -> freshSubstitution(c).sort}.toMap
        
        // Associate each function with a collection of fresh sorts
        val fnMap: Map[String, (Seq[Sort], Sort)] = theory.functionDeclarations.map { f => {
            Errors.precondition(f.argSorts.forall(!_.isBuiltin))
            val f_sub = freshSubstitution(f)
            f.name -> (f_sub.argSorts, f_sub.resultSort)
        }}.toMap
        
        val replacedAxioms = theory.axioms map freshSubstitution
        
        // Gather equations
        
        // Lookup the sort of a variable based on the current context
        def lookup(name: String, context: ContextStack): Option[Sort] = context match {
            case Nil => None
            case AnnotatedVar(Var(`name`), sort) :: tail => Some(sort)
            case _ :: tail => lookup(name, tail)
        }
        
        // Returns the sort of the term, and the set of equations
        def recur(term: Term, context: ContextStack): (Sort, Set[Equation]) = term match {
            case Top => (BoolSort, Set.empty)
            case Bottom => (BoolSort, Set.empty)
            case Var(name) => lookup(name, context) match {
                case Some(sort) => (sort, Set.empty)
                case None => (constantMap(name), Set.empty)
            }
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
                // All must be the same sort
                val newEqns = for(sort <- recurInfo.map(_._1)) yield Equation(recurInfo.head._1, sort)
                val eqns = recurInfo flatMap (_._2)
                (BoolSort, (eqns ++ newEqns).toSet)
            }
            case Implication(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
                Errors.assertion(pSort == BoolSort)
                Errors.assertion(qSort == BoolSort)
                (BoolSort, pEqns union qEqns)
            }
            case Iff(p, q) => {
                val (pSort, pEqns) = recur(p, context)
                val (qSort, qEqns) = recur(q, context)
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
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.assertion(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case Forall(avars, body) => {
                // Must put variables on context stack in reverse
                // e.g. (forall x: A, y: B, p(x, y)), the context should be
                // List[y: B, x: A]
                val newContext = avars.toList.reverse ::: context
                val (bodySort, bodyEqns) = recur(body, newContext)
                Errors.assertion(bodySort == BoolSort)
                (BoolSort, bodyEqns)
            }
            case EnumValue(_) => ???
            case DomainElement(_, _) => ???
            case BuiltinApp(_, _) => ???
            case IntegerLiteral(_) => ???
            case BitVectorLiteral(_, _) => ???
        }
        
        val recurInfo = replacedAxioms map {recur(_, List.empty)}
        val recurSorts = recurInfo map (_._1)
        Errors.assertion(recurSorts forall (_ == BoolSort))
        val equations = (recurInfo flatMap (_._2)).toList
        
        // Errors.assertion(false, equations.toString)
        
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
        object sortSubstitution extends SortApplication {
            override def apply(sort: Sort): Sort = sort match {
                case SortConst(indexStr) => {
                    val index = indexStr.toInt
                    val representative = unionFind.find(index)
                    sortVar(representative)
                }
                case BoolSort => BoolSort
                case _ => ???
            }
        }
        
        val newConstants: Set[AnnotatedVar] = theory.constants map (av => {
            Var(av.name) of sortSubstitution(constantMap(av.name))
        })
        
        val newFunctions: Set[FuncDecl] = theory.functionDeclarations map (f => {
            val (argSorts, resSort) = fnMap(f.name)
            val newArgSorts: Seq[Sort] = argSorts map sortSubstitution
            val newResSort = sortSubstitution(resSort)
            FuncDecl(f.name, newArgSorts, newResSort)
        })
        
        val newAxioms: Set[Term] = replacedAxioms map sortSubstitution
        
        val usedSorts: Set[Sort] = { for(i <- 0 to (freshSubstitution.index - 1)) yield sortVar(unionFind.find(i)) }.toSet
        
        val generalTheory = Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstants(newConstants)
            .withFunctionDeclarations(newFunctions)
            .withAxioms(newAxioms)
        
        val substitution = SortSubstitution.computeSigMapping(generalTheory.signature, theory.signature)
        
        (generalTheory, substitution)
    }
    
}
