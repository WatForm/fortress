package fortress.transformers

import fortress.msfol._

import scala.collection.mutable
import fortress.symmetry._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.problemstate.Scope

// for consistency with CLI string options, we have to have an object
// that does not have any options




case class SymmetryBreakingOptions(
    selectionHeuristic: SelectionHeuristic, // Heuristic for selecting order of functions
    breakSkolem: Boolean, // If true, breaks skolem functions and constants
    sortInference: Boolean, // If true, perform sort inference before symmetry breaking, then casts back to original sorts. Not necessary if symmetry breaking is performed previously
    patternOptimization: Boolean // If true, look for Portus patterns to optimize symmetry breaking
) {
    // def this(selectionHeuristic: SelectionHeuristic, breakSkolem: Boolean, sortInference: Boolean) {
    //     this(selectionHeuristic, breakSkolem, sortInference, patternOptimization = false)
    // }
}

// object SymmetryBreakingOptions{
//     def apply(selectionHeuristic: SelectionHeuristic, breakSkolem: Boolean, sortInference: Boolean): SymmetryBreakingOptions = SymmetryBreakingOptions(selectionHeuristic, breakSkolem, sortInference, patternOptimization = false)
// }

/** Applies symmetry breaking to the given Problem. The input Problem is allowed
* to have domain elements in its formulas. The output formula will have domain
* elements in its formulas. The resulting Problem has the same scopes, contains
* the original axioms plus additional symmetry breaking axioms, and is
* equisatisfiable to the original.
*/

object SymmetryBreakingOptionsDefaults extends 
    SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true
        ) {}

object SymmetryBreakingWithDefaultsTransformer 
 extends SymmetryBreakingTransformer(SymmetryBreakingOptionsDefaults) {}

class SymmetryBreakingTransformer(
    options: SymmetryBreakingOptions
) extends ProblemStateTransformer {

    def this(selectionHeuristic: SelectionHeuristic){
       this(SymmetryBreakingOptions(
            selectionHeuristic,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = false
        ))
    }

    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, flags) => {

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
            problemState
            .withTheory(newTheory)
            .addRangeRestrictions(newRangeRestrictions)
        }
    }

    // Performs symmetry breaking and returns tuple of (new declarations, new constraints, new range restrictions)
    private def symmetryBreak(theory: Theory, scopes: Map[Sort, Scope], selector: SelectionHeuristic, constantsToOmit: Set[AnnotatedVar], functionsToOmit: Set[FuncDecl]): (Seq[FuncDecl], Seq[Term], Set[RangeRestriction]) = {
        val tracker = if (options.patternOptimization) StalenessTracker.createWithPatternOptimization(theory, scopes)
        else StalenessTracker.create(theory, scopes)

        val newConstraints = new mutable.ListBuffer[Term]
        val newRangeRestrictions = new mutable.ListBuffer[RangeRestriction]
        val newDeclarations = new mutable.ListBuffer[FuncDecl]


        // val breaker = new DefaultSymmetryBreaker(theory, scopes, tracker)

        def addRangeRestrictions(rangeRestrictions: Set[RangeRestriction]): Unit = {
            // Add to constraints
            newConstraints ++= rangeRestrictions map (_.asFormula)
            newRangeRestrictions ++= rangeRestrictions
            // Add to used values
            for (restriction <- rangeRestrictions)
                tracker.markDomainElementsStale(restriction.asFormula)
        }

        def addGeneralConstraints(fmls: Set[Term]): Unit = {
            // Add to constraints
            newConstraints ++= fmls
            // Add to used values
            for (fml <- fmls) tracker.markDomainElementsStale(fml)
        }

        def addDeclaration(f: FuncDecl): Unit = {
            newDeclarations += f
        }

        def breakConstantsOfSort(sort: Sort, constants: IndexedSeq[AnnotatedVar]): Unit = {
            val constantRangeRestrictions = Symmetry.csConstantRangeRestrictions(sort, constants, tracker.state)
            val constantImplications = Symmetry.csConstantImplicationsSimplified(sort, constants, tracker.state)

            addRangeRestrictions(constantRangeRestrictions)
            addGeneralConstraints(constantImplications)
        }

        def breakConstants(constantsToBreak: Set[AnnotatedVar]): Unit = {
            for(sort <- theory.sorts if !sort.isBuiltin && scopes.contains(sort) && tracker.state.existsFreshValue(sort)) {
                breakConstantsOfSort(sort, constantsToBreak.filter(_.sort == sort).toIndexedSeq)
            }
        }

        def breakRDDFunction(f: FuncDecl): Unit = {
            val fRangeRestrictions = Symmetry.rddFunctionRangeRestrictions_UsedFirst(f, tracker.state)
            addRangeRestrictions(fRangeRestrictions)
        }

        def breakRDIFunction(f: FuncDecl): Unit = {
            val fRangeRestrictions = Symmetry.rdiFunctionRangeRestrictions(f, tracker.state)
            val fImplications = Symmetry.rdiFunctionImplicationsSimplified(f, tracker.state)
            addRangeRestrictions(fRangeRestrictions)
            addGeneralConstraints(fImplications)
        }

        def breakFunction(f: FuncDecl): Unit = {
            if( f.argSorts forall scopes.contains ) {
                if(tracker.state.existsFreshValue(f.resultSort)) {
                    if (f.isRDD) {
                        breakRDDFunction(f)
                    } else {
                        breakRDIFunction(f)
                    }
                }
            }
        }

        def breakPredicate(P: FuncDecl): Unit = {
            if(P.argSorts forall (tracker.state.numFreshValues(_) >= 2)) { // Need at least 2 unused values to do any symmetry breaking
                val pImplications = Symmetry.predicateImplications(P, tracker.state)
                addGeneralConstraints(pImplications)
            }
        }

        // First, perform symmetry breaking on constants
        breakConstants(theory.constantDeclarations diff constantsToOmit)

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
            selector.nextFunctionPredicate(tracker.state, remaining) match {
                case None => ()
                case Some(p @ FuncDecl(_, _, BoolSort)) => {
                    if( p.argSorts forall scopes.contains ) {
                        breakPredicate(p)
                        loop(usedFunctionsPredicates + p)
                    }
                }
                case Some(f) => {
                    breakFunction(f)
                    loop(usedFunctionsPredicates + f)
                }
            }
        }

        loop(Set.empty)
        (newDeclarations.toList, newConstraints.toList, newRangeRestrictions.toSet)
    }
    /*
    val name: String = s"Symmetry Breaking Transformer (${options})"
    */
}
