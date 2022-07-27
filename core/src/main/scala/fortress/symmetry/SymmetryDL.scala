package fortress.symmetry

import fortress.msfol.DSL._
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.util.Extensions._

import scala.collection.mutable

/** Generate symmetry breaking constraints with disjunctions limit
  */
object SymmetryDL {
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
                                     state: StalenessState,
                                     disjunctsLimit: Option[Int] = None
                                   ): Set[RangeRestriction] = {

        Errors.Internal.precondition(!sort.isBuiltin)
        Errors.Internal.precondition(constants.forall(_.sort == sort))

        val n = constants.size
        var m = state.numFreshValues(sort)
        if (disjunctsLimit.isDefined) {
            if (state.staleValues(sort).size >= disjunctsLimit.get) return Set.empty
            m = scala.math.min(m, disjunctsLimit.get - state.staleValues(sort).size)
        }
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
                                          state: StalenessState,
                                          numRangeFormulaAdded: Int = Int.MaxValue
                                        ): Set[Term] = {

        Errors.Internal.precondition(!sort.isBuiltin)
        Errors.Internal.precondition(constants.forall(_.sort == sort))

        val freshValues = state.freshValues(sort)

        val n = constants.size
        val m = scala.math.min(state.numFreshValues(sort), numRangeFormulaAdded)
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
                                      state: StalenessState,
                                      disjunctsLimit: Option[Int] = None
                                    ): Set[RangeRestriction] = {

        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(f.isRDI)

        val freshResultValues: IndexedSeq[DomainElement] = state.freshValues(f.resultSort)
        val staleResultValues = state.staleValues(f.resultSort)

        var m = freshResultValues.size
        if (disjunctsLimit.isDefined) {
            if (state.staleValues(f.resultSort).size >= disjunctsLimit.get) return Set.empty
            m = scala.math.min(m, disjunctsLimit.get - state.staleValues(f.resultSort).size)
        }

        val argumentListsIterable: Iterable[ArgList] =
//            new fortress.util.ArgumentListGenerator(state.scope(_)._1)
            new fortress.util.ArgumentListGenerator( state.scope(_).asInstanceOf[BoundedScope].value)
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
                                           state: StalenessState,
                                           numRangeFormulaAdded: Int = Int.MaxValue
                                         ): Set[Term] = {

        Errors.Internal.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.Internal.precondition(!f.resultSort.isBuiltin)
        Errors.Internal.precondition(!(f.argSorts contains f.resultSort))
        Errors.Internal.precondition(f.isRDI)

        val freshResultValues: IndexedSeq[DomainElement] = state.freshValues(f.resultSort)

        val m = scala.math.min(freshResultValues.size, numRangeFormulaAdded)

        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(state.scope(_).asInstanceOf[BoundedScope].value)
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


    private[this] def predicateImplicationChain(
                                                 P: FuncDecl,
                                                 argLists: IndexedSeq[ArgList]
                                               ): Seq[Term] = {

        for (i <- 1 to (argLists.size - 1)) yield {
            App(P.name, argLists(i)) ==> App(P.name, argLists(i - 1))
        }
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
                               state: StalenessState,
                               numFormulasToAdd: Option[Int] = None
                             ): Set[Term] = {

        Errors.Internal.precondition(P.resultSort == BoolSort)
        Errors.Internal.precondition(P.argSorts forall (!_.isBuiltin))
        Errors.Internal.precondition(P.argSorts exists (state.numFreshValues(_) >= 2))

        val tracker = state.createTrackerWithState

        def fillArgList(sort: Sort, d: DomainElement): ArgList = {
            Errors.Internal.precondition(d.sort == sort)
            for (s <- P.argSorts) yield {
                if (s == sort) d
                else DomainElement(1, s) // TODO can we make a smarter selection for the other elements?
            }
        }

        val constraints = new mutable.ListBuffer[Term]
        var argSorts = P.argSorts

        while (argSorts exists (tracker.state.numFreshValues(_) >= 2)) {
            val sort = (argSorts find (tracker.state.numFreshValues(_) >= 2)).get
            var r = tracker.state.numFreshValues(sort)
            if (numFormulasToAdd.isDefined) {
                r = scala.math.min(tracker.state.numFreshValues(sort), numFormulasToAdd.get + 1)
            }
            val argLists: IndexedSeq[ArgList] = for (i <- 0 to (r - 1)) yield {
                fillArgList(sort, tracker.state.freshValues(sort)(i))
            }
            val implications = predicateImplicationChain(P, argLists)
            constraints ++= implications
            tracker.markStale(implications flatMap (_.domainElements))
            argSorts = argSorts.filterNot(_ == sort)
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
                                                     argumentOrder: IndexedSeq[DomainElement],
                                                     disjunctsLimit: Option[Int] = None
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
                if (sort == f.resultSort) resVal
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
            if (unused.nonEmpty) {
                val input = argumentOrder(index)
                val (rangeRestriction, newlyUsed) = constraintForInput(input, unused, used)
                if (disjunctsLimit.isEmpty || rangeRestriction.values.size <= disjunctsLimit.get) {
                    rangeRestrictions += rangeRestriction
                    loop(index + 1, unused diff newlyUsed, used ++ newlyUsed)
                }
            }
        }

        loop(0, state.freshValues(f.resultSort), state.staleValues(f.resultSort))

        rangeRestrictions.toSet
    }

    def rddFunctionRangeRestrictions_UnusedFirst(
                                                  f: FuncDecl,
                                                  state: StalenessState,
                                                  disjunctsLimit: Option[Int] = None
                                                ): Set[RangeRestriction] = {
        rddFunctionRangeRestrictionsGeneral(f, state, state.freshValues(f.resultSort), disjunctsLimit)
    }

    def rddFunctionRangeRestrictions_UsedFirst(
                                                f: FuncDecl,
                                                state: StalenessState,
                                                disjunctsLimit: Option[Int] = None
                                              ): Set[RangeRestriction] = {
        rddFunctionRangeRestrictionsGeneral(
            f,
            state,
            state.staleValues(f.resultSort) ++ state.freshValues(f.resultSort),
            disjunctsLimit
        )
    }

}
