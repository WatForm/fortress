package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.util.Extensions._
import fortress.msfol.DSL._

import scala.collection.mutable

object Symmetry {
    private[this] type ArgList = Seq[Value]

    /** Produces constant range restrictions for one sort like the following:
      *
      * c1 = stale values + a1
      * c2 ∈ stale values + {a1,a2}
      * c3 ∈ stale values + {a1,a2,a3}
      * ...
      */
    def csConstantRangeRestrictions(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        state: StalenessState
    ): Set[RangeRestriction] = {
        
        Errors.Internal.precondition(!sort.isBuiltin)
        Errors.Internal.precondition(constants.forall(_.sort == sort))
        
        val n = constants.size
        val m = state.numFreshValues(sort)
        val r = scala.math.min(n, m)
        
        val constraints: Seq[RangeRestriction] =
            for (k <- 0 to (r - 1)) // Enumerate constants
            yield {
                val c_k = constants(k).variable
            
                val possibleValues: Seq[DomainElement] =
                    state.staleValues(sort) ++ // Could be any of the stale values
                    state.freshValues(sort).take(k + 1) // One of the first k + 1 fresh values (recall, k starts at 0)
            
                RangeRestriction(c_k, possibleValues)
            }
        
        constraints.toSet
    }

    /** Produces matching output to csConstantRangeRestrictions - meant to be
      * used at same time with same input. Sample constant implications are like
      * the following:
      *
      * c2 = a2 ==> a1 = c1
      *
      * c3 = a3 ==> a2 ∈ {c1,c2}
      * c3 = a2 ==> a1 ∈ {c1,c2}
      *
      * c4 = a4 ==> a3 ∈ {c1,c2,c3}
      * c4 = a3 ==> a2 ∈ {c1,c2,c3}
      * c4 = a2 ==> a1 ∈ {c1,c2,c3}
      * ...
      */
    def csConstantImplications(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        state: StalenessState,
    ): Set[Term] = {
        
        Errors.Internal.precondition(!sort.isBuiltin)
        Errors.Internal.precondition(constants.forall(_.sort == sort))
        
        val freshValues = state.freshValues(sort)
        
        val n = constants.size
        val m = state.numFreshValues(sort)
        val r = scala.math.min(n, m)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates constants
            j <- 1 to i // Enumerates values, starting with the second
        } yield {
            val c_i = constants(i).variable
            
            val precedingConstants = constants.take(i) map (_.variable) // Recall indexing starts at 0
            
            (c_i === freshValues(j)) ==> (freshValues(j - 1) equalsOneOfFlip precedingConstants)
        }
        
        implications.toSet
    }

    /** Produces matching output to csConstantRangeRestrictions - meant to be
      * used at same time with same input. Sample simplified constant
      * implications are like the following:
      *
      * c2 = a2 ==> a1 = c1
      *
      * c3 = a3 ==> a2 = c2
      * c3 = a2 ==> a1 ∈ {c1,c2}
      *
      * c4 = a4 ==> a3 = c3
      * c4 = a3 ==> a2 ∈ {c2,c3}
      * c4 = a2 ==> a1 ∈ {c1,c2,c3}
      * ...
      */
    def csConstantImplicationsSimplified(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        state: StalenessState
    ): Set[Term] = {
        
        Errors.Internal.precondition(!sort.isBuiltin)
        Errors.Internal.precondition(constants.forall(_.sort == sort))
        
        val freshValues = state.freshValues(sort)
        
        val n = constants.size
        val m = state.numFreshValues(sort)
        val r = scala.math.min(n, m)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates constants
            j <- 1 to i // Enumerates values, starting with the second
        } yield {
            val c_i = constants(i).variable
            
            val possiblePrecedingConstants = constants.rangeSlice((j - 1) to (i - 1)).map(_.variable)
            
            (c_i === freshValues(j)) ==> (freshValues(j - 1) equalsOneOfFlip possiblePrecedingConstants)
        }
        
        implications.toSet
    }

    /** Produces range restrictions for range-domain independent function.
      * Sample rdi range restrictions are like the following:
      *
      * f(t1) = stale values + a1
      * f(t2) ∈ stale values + {a1,a2}
      * f(t3) ∈ stale values + {a1,a2,a3}
      * ...
      */
    def rdiFunctionRangeRestrictions(
        f: FuncDecl,
        state: StalenessState
    ): Set[RangeRestriction] = {
        
        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(f.isRDI)
        
        val freshResultValues: IndexedSeq[DomainElement] = state.freshValues(f.resultSort)
        val staleResultValues = state.staleValues(f.resultSort)
        
        val m = freshResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(state.scope(_))
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them, for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        
        val n = argumentLists.size
        val r = scala.math.min(m, n)
        
        val constraints: Seq[RangeRestriction] =
            for (k <- 0 to (r - 1)) // Enumerate argument vectors
            yield {
                val argList = argumentLists(k)
                val possibleResultValues: Seq[DomainElement] = 
                    staleResultValues ++ // Could be any of the stale values
                    freshResultValues.take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
                RangeRestriction(App(f.name, argList), possibleResultValues)
            }
        
        constraints.toSet
    }

    /** Produces matching output to rdiFunctionRangeRestrictions - meant to be
      * used at same time with same input. Sample rdi function implications are
      * like the following:
      *
      * f(t2) = a2 ==> a1 = f(t1)
      *
      * f(t3) = a3 ==> a2 ∈ {f(t1),f(t2)}
      * f(t3) = a2 ==> a1 ∈ {f(t1),f(t2)}
      *
      * f(t4) = a4 ==> a3 ∈ {f(t1),f(t2),f(t3)}
      * f(t4) = a3 ==> a2 ∈ {f(t1),f(t2),f(t3)}
      * f(t4) = a2 ==> a1 ∈ {f(t1),f(t2),f(t3)}
      */
    def rdiFunctionImplications(
        f: FuncDecl,
        state: StalenessState
    ): Set[Term] = {
        
        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(!(f.argSorts contains f.resultSort))
        
        val freshResultValues: IndexedSeq[DomainElement] = state.freshValues(f.resultSort)
        
        val m = freshResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(state.scope(_))
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them,  for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        val applications: IndexedSeq[Term] = argumentLists map (App(f.name, _))
        
        val n = applications.size
        
        val r = scala.math.min(m, n)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates argVectors
            j <- 1 to i // Enumerates result values, starting with the second
        } yield {
            val app_i = applications(i)
            
            val precedingApps = applications.take(i) // Recall indexing starts at 0
            
            (app_i === freshResultValues(j)) ==> (freshResultValues(j - 1) equalsOneOfFlip precedingApps)
        }
        
        implications.toSet
    }

    /** Produces matching output to rdiFunctionRangeRestrictions - meant to be
      * used at same time with same input. Sample simplified rdi function
      * implications are like the following:
      *
      * f(t2) = a2 ==> a1 = f(t1)
      *
      * f(t3) = a3 ==> a2 = f(t2)
      * f(t3) = a2 ==> a1 ∈ {f(t1),f(t2)}
      *
      * f(t4) = a4 ==> a3 = f(t3)
      * f(t4) = a3 ==> a2 ∈ {f(t2),f(t3)}
      * f(t4) = a2 ==> a1 ∈ {f(t1),f(t2),f(t3)}
      */
    def rdiFunctionImplicationsSimplified(
        f: FuncDecl,
        state: StalenessState
    ): Set[Term] = {
        
        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(!(f.argSorts contains f.resultSort))
        Errors.Internal.precondition(f.isRDI)
        
        val freshResultValues: IndexedSeq[DomainElement] = state.freshValues(f.resultSort)
        
        val m = freshResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(state.scope(_))
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them, for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        val applications: IndexedSeq[Term] = argumentLists map (App(f.name, _))
        
        val n = applications.size
        
        val r = scala.math.min(m, n)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates argVectors
            j <- 1 to i // Enumerates result values, starting with the second
        } yield {
            val app_i = applications(i)
            val possiblePrecedingApps = applications.rangeSlice((j - 1) to (i - 1))
            (app_i === freshResultValues(j)) ==> (freshResultValues(j - 1) equalsOneOfFlip possiblePrecedingApps)
        }
        
        implications.toSet
    }

    // Helper method used by method rainbowFunctionLT
    def sortLtDefinition(sort: Sort, scope: Int): (FuncDecl, Seq[Term])  = {
        val LT = "_LT" + sort.name
        val assertions = for {
            i <- 1 to scope
            j <- 1 to scope
        } yield {
            val app = App(LT, DomainElement(i, sort), DomainElement(j, sort))
            if (i <= j) app
            else Not(app)
        }
        (FuncDecl(LT, sort, sort, BoolSort), assertions)
    }

    // Function used in experimental symmetry breakers
    // I don't think that I can say the constants are ordered
    // No input elements to shuffle
    def rainbowFunctionLT(
        f: FuncDecl,
        state: StalenessState
    ): (FuncDecl, Seq[Term], Seq[RangeRestriction]) = {
        
        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        
        Errors.Internal.precondition(f.isRainbowSorted)
        Errors.Internal.precondition(f.arity <= 2)
        Errors.Internal.precondition(f.argSorts forall (state.staleValues(_).isEmpty))
        Errors.Internal.precondition(state.staleValues(f.resultSort).isEmpty)
        Errors.Internal.precondition(f.argSorts.forall(state.scope(_) >= 2))
        Errors.Internal.precondition(state.scope(f.resultSort) >= 2)
        
        val (ltDecl, ltDefn) = sortLtDefinition(f.resultSort, state.scope(f.resultSort))
        
        val LT = ltDecl.name
        
        val (constraints, rangeRestrictions): (Seq[Term], Seq[RangeRestriction]) = f match {
            // Unary
            case FuncDecl(fname, Seq(argSort), resultSort) => {
                // Ordering constraints
                val ltConstraints: Seq[Term] = for(i <- 1 until state.scope(argSort)) yield {
                    App(LT,
                        App(fname, DomainElement(i, argSort)),
                        App(fname, DomainElement(i + 1, argSort))
                    )
                }
                
                val rdiRangeRestrictions: Seq[RangeRestriction] = rdiFunctionRangeRestrictions(f, state).toSeq
                val rdiImplicationsSimplified: Seq[Term] = rdiFunctionImplicationsSimplified(f, state).toSeq
                
                (ltConstraints ++ rdiImplicationsSimplified, rdiRangeRestrictions)
            }
            // Binary
            case FuncDecl(fname, Seq(argSort1, argSort2), resultSort) => {
                
                // First argument constraints
                
                // Ordering constraints on first argument
                val ltConstraintsArg1: Seq[Term] = for(i <- 1 until state.scope(argSort1)) yield {
                    App(LT,
                        App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)),
                        App(fname, DomainElement(i + 1, argSort1), DomainElement(1, argSort2))
                    )
                }
                
                // Have to make rdi constraints manually, otherwise:
                // 1. ordering might not match what we want
                // 2. if scope(resultSort) > scope(argSort1), the constraints will spill over into the second
                // value of argSort2, which is not what we want because then we can't justify "shuffling"
                
                val r1 = scala.math.min(state.scope(argSort1), state.scope(resultSort))
                
                val rdiRangeRestrictions: Seq[RangeRestriction] = for(i <- 1 to r1) yield {
                    RangeRestriction(
                        App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)),
                        DomainElement.range(1 to i, resultSort)
                    )
                }
                
                val rdiImplicationsSimplified: Seq[Term] = for {
                    i <- 1 to r1
                    j <- 2 to i
                } yield {
                    val lhs = App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)) === DomainElement(j, resultSort)
                    val rhs = DomainElement(j - 1, resultSort) equalsOneOfFlip DomainElement.range((j - 1) to (i - 1), argSort1).map(App(fname, _, DomainElement(1, argSort2)))
                    lhs ==> rhs
                }
                
                // Second argument constraints
                val ltConstraintsArg2: Seq[Term] = for(i <- 2 until state.scope(argSort2)) yield {
                    App(LT,
                        App(fname, DomainElement(1, argSort1), DomainElement(i, argSort2)),
                        App(fname, DomainElement(1, argSort1), DomainElement(i + 1, argSort2))
                    )
                }
                
                (ltConstraintsArg1 ++ ltConstraintsArg2 ++ rdiImplicationsSimplified, rdiRangeRestrictions)
            }
            // Other
            case _ => (???, ???)
        }
        
        (ltDecl, ltDefn ++ constraints, rangeRestrictions)
    }
    
    private[this] def predicateImplicationChain(
        P: FuncDecl,
        argLists: IndexedSeq[ArgList]
    ): Seq[Term] = {
        
        for(i <- 1 to (argLists.size - 1)) yield {
            App(P.name, argLists(i)) ==> App(P.name, argLists(i - 1))
        }
    }
    
    // I think better symmetry breaking can be done on predicates.
    // This is about as good as we can do for predicates of the form P: A -> Bool
    // Or P: A x A -> Bool, but I think more can be done for e.g. P: A x B x A -> Bool
    // The issue is the smallest element comment below.
    def predicateImplications_OLD(
        P: FuncDecl,
        state: StalenessState
    ): Set[Term] = {
        
        Errors.Internal.precondition(P.resultSort == BoolSort)
        Errors.Internal.precondition(P.argSorts.forall(!_.isBuiltin))
        
        Errors.Internal.precondition(P.argSorts forall (state.numFreshValues(_) >= 2))
        
        val r = (P.argSorts map (state.numFreshValues(_))).min // Smallest number of unused values
        
        // Generate lists of arguments in the order we will use them for symmetry breaking
        // e.g. If P: A x B x A -> Bool, gives Seq[(a1, b1, a1), (a2, b2, a2), ...]
        
        val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
            P.argSorts map (sort => state.freshValues(sort)(i))
        }
        
        predicateImplicationChain(P, argLists).toSet
    }

    /** Produces predicate implications, which known as ladder implications:
      *
      * Q(a2) ==> Q(a1)
      * Q(a3) ==> Q(a2)
      * ···
      * Q(am) ==> Q(am−1)
      */
    def predicateImplications(
        P: FuncDecl,
        state: StalenessState
    ): Set[Term] = {
            
            Errors.Internal.precondition(P.resultSort == BoolSort)
            Errors.Internal.precondition(P.argSorts forall (!_.isBuiltin))
            Errors.Internal.precondition(P.argSorts exists (state.numFreshValues(_) >= 2))
            
            val tracker = state.createTrackerWithState
            
            def fillArgList(sort: Sort, d: DomainElement): ArgList = {
                Errors.Internal.precondition(d.sort == sort)
                for(s <- P.argSorts) yield {
                    if(s == sort) d
                    else DomainElement(1, s) // TODO can we make a smarter selection for the other elements?
                }
            }
            
            val constraints = new mutable.ListBuffer[Term]
            
            while(P.argSorts exists (tracker.state.numFreshValues(_) >= 2)) {
                val sort = (P.argSorts find (tracker.state.numFreshValues(_) >= 2)).get
                val r = tracker.state.numFreshValues(sort)
                val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
                    fillArgList(sort, tracker.state.freshValues(sort)(i))
                }
                val implications = predicateImplicationChain(P, argLists)
                constraints ++= implications
                tracker.markStale(implications flatMap (_.domainElements))
            }
            
            constraints.toSet
        }

    /** Produces range restrictions for range-domain dependent function as the
      * following iteratively:
      *
      * f(a) ∈ Stale(A) ∪ {a, a∗}
      * where a∗ is an arbitrary representative of Fresh(A) \ {a}
      */
    private def rddFunctionRangeRestrictionsGeneral(
        f: FuncDecl,
        state: StalenessState,
        argumentOrder: IndexedSeq[DomainElement]
    ): Set[RangeRestriction] = {

        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(f.argSorts contains f.resultSort)
        Errors.Internal.precondition(!f.isRDI)

        // We fix particular values for the sorts not in the output
        // These stay the same for all argument lists we symmetry break using
        // (you don't have to fix particular values, but you can)
        
        // Construct an argument list given the result value we are using
        // e.g. if f: A x B x A x D -> A,
        // given a2 it will yield: (a2, b1, a2, d1)
        // given a3 it will yield: (a3, b1, a3, d1)
        def constructArgList(resVal: DomainElement): Seq[DomainElement] = {
            Errors.Internal.precondition(resVal.sort == f.resultSort)
            f.argSorts map (sort => {
                if(sort == f.resultSort) resVal
                else DomainElement(1, sort) // for other sorts, doesn't matter what values we choose
            })
        }

        def constraintForInput(
            input: DomainElement,
            unusedResultValues: IndexedSeq[DomainElement],
            usedResultValues: IndexedSeq[DomainElement]
        ): (RangeRestriction, IndexedSeq[DomainElement]) = {
            val argList = constructArgList(input)

            val possibleResultValues: IndexedSeq[DomainElement] =
                (usedResultValues :+ // Could be any of the used values
                input) ++ // Or itself
                Seq(unusedResultValues.find(_ != input)).flatten // Or the first unused value that is not itself
            
            val rangeRestriction = RangeRestriction(App(f.name, argList), possibleResultValues.distinct)
            val newlyUsed = possibleResultValues diff usedResultValues
            (rangeRestriction, newlyUsed)
        }

        val rangeRestrictions = mutable.Set[RangeRestriction]()

        @scala.annotation.tailrec
        def loop(index: Int, unused: IndexedSeq[DomainElement], used: IndexedSeq[DomainElement]): Unit = {
            if(unused.nonEmpty) {
                val input = argumentOrder(index)
                val (rangeRestriction, newlyUsed) = constraintForInput(input, unused, used)
                rangeRestrictions += rangeRestriction
                loop(index + 1, unused diff newlyUsed, used ++ newlyUsed)
            }
        }
        loop(0, state.freshValues(f.resultSort), state.staleValues(f.resultSort))

        rangeRestrictions.toSet
    }

    def rddFunctionRangeRestrictions_UnusedFirst(
        f: FuncDecl,
        state: StalenessState
    ): Set[RangeRestriction] = {
        rddFunctionRangeRestrictionsGeneral(f, state, state.freshValues(f.resultSort))
    }

    def rddFunctionRangeRestrictions_UsedFirst(
        f: FuncDecl,
        state: StalenessState
    ): Set[RangeRestriction] = {
        rddFunctionRangeRestrictionsGeneral(
            f,
            state,
            state.staleValues(f.resultSort) ++ state.freshValues(f.resultSort)
        )
    }
    
}
