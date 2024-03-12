package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.problemstate.Scope

case class SymmetryBreakingOptions(
    selectionHeuristic: SelectionHeuristic, // Heuristic for selecting order of functions
    symmetryBreakerFactory: SymmetryBreakerFactory,
    breakSkolem: Boolean, // If true, breaks skolem functions and constants
    sortInference: Boolean // If true, perform sort inference before symmetry breaking, then casts back to original sorts. Not necessary if symmetry breaking is performed previously
)

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/
class SymmetryBreakingTransformer(
    options: SymmetryBreakingOptions
) extends ProblemStateTransformer {

    def this(selectionHeuristic: SelectionHeuristic, symmetryBreakerFactory: SymmetryBreakerFactory){
       this(SymmetryBreakingOptions(
            selectionHeuristic,
            symmetryBreakerFactory,
            breakSkolem = true,
            sortInference = false
        ))
    }
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            val (newDecls, newConstraints, newRangeRestrictions) = if(options.sortInference) {
                // Perform sort inference first
                val (infTheory, substitution) = theory.inferSorts
                val infScopes = {
                    for { sort <- infTheory.sorts if !sort.isBuiltin }
                    yield {sort -> scopes(substitution(sort))}
                }.toMap
                // If sort substitution is identity, perform symmetry breaking as normal
                if(substitution.isIdentity) {
                    val constantsToOmit: Set[AnnotatedVar] = if(options.breakSkolem) Set() else skc
                    val functionsToOmit: Set[FuncDecl] = if(options.breakSkolem) Set() else skf 
                    symmetryBreak(theory, scopes, options.selectionHeuristic, constantsToOmit, functionsToOmit)
                } else {
                    val constantsToOmit: Set[AnnotatedVar] = if(options.breakSkolem) Set() else ???
                    val functionsToOmit: Set[FuncDecl] = if(options.breakSkolem) Set() else ???
                    // Perform symmetry breaking on inferred theory, but select as if it wasn't there
                    val selector = new SelectAfterSubstitution(options.selectionHeuristic, substitution, theory.signature, infTheory.signature)
                    val (generalDecls, generalConstraints, generalRangeRestrictions) = symmetryBreak(infTheory, infScopes, selector, constantsToOmit, functionsToOmit)
                    (generalDecls.map(substitution), generalConstraints.map(substitution), generalRangeRestrictions.map( (rr: RangeRestriction) => substitution(rr)))
                }
            } else {
                val constantsToOmit: Set[AnnotatedVar] = if(options.breakSkolem) Set() else skc
                val functionsToOmit: Set[FuncDecl] = if(options.breakSkolem) Set() else skf 
                symmetryBreak(theory, scopes, options.selectionHeuristic, constantsToOmit, functionsToOmit)
            }
            
            // Add symmetry breaking function declarations, constraints, and range restrictions
            val newTheory = theory.withFunctionDeclarations(newDecls).withAxioms(newConstraints)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts union newRangeRestrictions, unapplyInterp, distinctConstants)
        }
    }
    
    // Performs symmetry breaking and returns tuple of (new declarations, new constraints, new range restrictions)
    private def symmetryBreak(theory: Theory, scopes: Map[Sort, Scope], selector: SelectionHeuristic, constantsToOmit: Set[AnnotatedVar], functionsToOmit: Set[FuncDecl]): (Seq[FuncDecl], Seq[Term], Set[RangeRestriction]) = {
        val breaker = options.symmetryBreakerFactory.create(theory, scopes)


        // First, perform symmetry breaking on constants
        breaker.breakConstants(theory.constantDeclarations diff constantsToOmit)
        
        // This weirdness exists to make sure that this version performs symmetry breaking
        // on functions in the same order as the previous version
        // It is only here for the sake of consistency
        val functions = theory.functionDeclarations filter { fn => {
            (!fn.resultSort.isBuiltin && scopes.contains(fn.resultSort)) && (fn.argSorts forall (!_.isBuiltin)) && (fn.argSorts forall scopes.contains)
        }}
        val predicates = theory.functionDeclarations.filter { fn => {
            (fn.resultSort == BoolSort) && (fn.argSorts forall (!_.isBuiltin)) && (fn.argSorts forall scopes.contains)
        }}
        
        val fp = scala.collection.immutable.ListSet( (functions.toList ++ predicates.toList) : _* )
        // END OF WEIRDNESS
            .diff(functionsToOmit)

        // Then, perform symmetry breaking on functions and predicates
        @scala.annotation.tailrec
        def loop(usedFunctionsPredicates: Set[FuncDecl]): Unit = {
            val remaining = fp diff usedFunctionsPredicates
            selector.nextFunctionPredicate(breaker.stalenessState, remaining) match {
                case None => ()
                case Some(p @ FuncDecl(_, _, BoolSort)) => {
                    if( p.argSorts forall scopes.contains ) {
                        breaker.breakPredicate(p)
                        loop(usedFunctionsPredicates + p)
                    }
                }
                case Some(f) => {
                    breaker.breakFunction(f)
                    loop(usedFunctionsPredicates + f)
                }
            }
        }
        
        loop(Set.empty)
        (breaker.declarations, breaker.constraints, breaker.rangeRestrictions.toSet)
    }

    val name: String = s"Symmetry Breaking Transformer (${options})" 
}
