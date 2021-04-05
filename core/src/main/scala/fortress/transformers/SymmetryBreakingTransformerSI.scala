package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import scala.collection.immutable.ListSet

// TODO: move this into a symmetry breaker

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/
class SymmetryBreakingTransformerSI(
    selectionHeuristic: SelectionHeuristic,
    symmetryBreakerFactory: SymmetryBreakerFactory
) extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp) => {

            // Perform sort inference first
            val (infTheory, substitution) = theory.inferSorts
            val infScopes = {
                for { sort <- infTheory.sorts if !sort.isBuiltin }
                yield {sort -> scopes(substitution(sort))}
            }.toMap

            if(substitution.isIdentity) return (new SymmetryBreakingTransformer(selectionHeuristic, symmetryBreakerFactory)).apply(problemState)

            // Perform symmetry breaking on the original problem, to see what order of constants/functions we would have gotten.
            def getOrderings: (IndexedSeq[AnnotatedVar], IndexedSeq[FuncDecl]) = {
                val breaker = symmetryBreakerFactory.create(theory, scopes)
            
                val constantOrder = breaker.breakConstants(theory.constants)
                
                // This weirdness exists to make sure that this version performs symmetry breaking
                // on functions in the same order as the previous version
                // It is only here for the sake of consistency
                val functions = theory.functionDeclarations filter { fn => {
                    (!fn.resultSort.isBuiltin) && (fn.argSorts forall (!_.isBuiltin))
                }}
                val predicates = theory.functionDeclarations.filter { fn => {
                    (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin))
                }}
                
                val fp = scala.collection.immutable.ListSet( (functions.toList ++ predicates.toList) : _* )
                // END OF WEIRDNESS
                
                val fnOrder = new scala.collection.mutable.ListBuffer[FuncDecl]()

                @scala.annotation.tailrec
                def loop(usedFunctionsPredicates: Set[FuncDecl]): Unit = {
                    val remaining = fp diff usedFunctionsPredicates
                    selectionHeuristic.nextFunctionPredicate(breaker.stalenessState, remaining) match {
                        case None => ()
                        case Some(p @ FuncDecl(_, _, BoolSort)) => {
                            fnOrder += p
                            breaker.breakPredicate(p)
                            loop(usedFunctionsPredicates + p)
                        }
                        case Some(f) => {
                            fnOrder += f
                            breaker.breakFunction(f)
                            loop(usedFunctionsPredicates + f)
                        }
                    }
                }
                
                loop(Set.empty)
                (constantOrder, fnOrder.toIndexedSeq)
            }

            val (constantOrder, fnOrder) = getOrderings

            val constantOrder_inf = constantOrder.map(av => infTheory.signature.constants.find(_.name == av.name).get)
            val fnOrder_inf = fnOrder.map(f => infTheory.signature.functionWithName(f.name).get)

            // println(constantOrder_inf.mkString("\n"))
            // println(fnOrder_inf.mkString("\n"))

            // Perform symmetry breaking on inferred theory
            val breaker = symmetryBreakerFactory.create(infTheory, infScopes)

            // Do constants in the order they would be done in the original theory
            // do other constants only after those ones are finished
            val order = breaker.breakConstantsPreOrdered(constantOrder_inf ++ infTheory.constants.toIndexedSeq.diff(constantOrder_inf))
            // println(order.mkString("\n"))

            // Do functions in the order they would be done in the original theory
            for(fn <- fnOrder_inf) {
                fn match {
                    case p @ FuncDecl(_, _, BoolSort) => {
                        breaker.breakPredicate(p)
                    }
                    case f => {
                        breaker.breakFunction(f)
                    }
                }
            }

            // Do any remaining functions now
            val fp = ListSet(infTheory.functionDeclarations.toIndexedSeq.diff(fnOrder_inf) :_*)
            @scala.annotation.tailrec
            def loop(usedFunctionsPredicates: Set[FuncDecl]): Unit = {
                val remaining = fp diff usedFunctionsPredicates
                selectionHeuristic.nextFunctionPredicate(breaker.stalenessState, remaining) match {
                    case None => ()
                    case Some(p @ FuncDecl(_, _, BoolSort)) => {
                        breaker.breakPredicate(p)
                        loop(usedFunctionsPredicates + p)
                    }
                    case Some(f) => {
                        breaker.breakFunction(f)
                        loop(usedFunctionsPredicates + f)
                    }
                }
            }
            
            loop(Set.empty)

            // Apply substitution to go back to original theory
            val newDecls = breaker.declarations.map(substitution)
            val newConstraints = breaker.constraints.map(substitution)
            val newRangeRestrictions = breaker.rangeRestrictions.toSet.map( (rr: RangeRestriction) => substitution(rr))
            
            val newTheory = theory.withFunctionDeclarations(newDecls).withAxioms(newConstraints)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions, unapplyInterp)
        }
    }
    
    val name: String = s"Symmetry Breaking Transformer SI (${selectionHeuristic.name})" 
}
